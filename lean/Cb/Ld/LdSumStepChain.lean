-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSumStepChain.lean: all rounds in which tables of words are folded (in this library: the
rounds of the sumcheck of Cb/Ld/LdSum.lean), stated on words, with one extractor that undoes them
from the last to the first.

Definitions and statements (each a `Prop` in `Cb.Spec`); the proofs are in
Cb/Ld/LdSumStepChainProofs.lean. A halving (`Halving`, Cb/Ld/LdSumStep.lean) tells how a word and a
pair (message, randomness) of the code before a round split into two of the code after it. A stage
(`LdCode.stg`, Cb/Ld/LdSumStepStage.lean) is three codes side by side: C with rows on the cube of k
variables, Z and Zw (the two masks) with rows on the cube of h variables.

Main names:
 1. The bad values of one round, named. `H.BadAt e Φ Φ' f γ`: γ is exceptional for the two halves of
    f, or some member of the list around f with a false claim Φ gets a true claim Φ' when it is
    folded at γ. `Spec.ldh_badAt_cnt`: under the hypotheses of its statement, at most bad + L κ
    values are bad (the count of `Spec.lds_round`, Cb/Ld/LdSumStep.lean). `Spec.ldh_good`: under
    `D'.Laws`, `D'.Dist d`, `H.Laws d` and e < d, at a value that is not bad, every w' near the fold
    with a true claim goes back to a w near f, with a true claim, that folds to w'.
 2. A chain of halvings (`HChain D D''`): nothing, or a halving followed by a chain. A point of a
    chain is a nested pair (γ, rest). `c.foldAll`, `c.foldAllW`: all folds, one after the other.
    `c.backAll`: the extractor of all rounds, from the last round to the first; for each round it
    needs the word before that round, which it computes from f and the point. `c.OK d`: the code
    after each round has its laws and the distance d, the halvings have their laws.
    `Spec.ldh_chain`: under e < d and `c.OK d`, if no round is bad (`c.Bad`, for claims
      `cl : c.Claims`), `c.backAll` takes every witness at the end (near the last word, last claim
      true) to a witness at the start (near f, first claim true), and the result folds back to that
      witness.
 3. The stages (Cb/Ld/LdSumStepStage.lean). `Halving.step C Z Zw k h`: from the stage (k + 1, h) to
    the stage (k, h - 1): all three tables are halved if h > 0, else the masks rest.
    `stgChain C Z Zw k h`: the k rounds from the stage (k, h); it ends at the stage (0, endH k h),
    and endH k h = 0 if h ≤ k (`Spec.ldh_endH`). No cast of types is in these terms, for any k and h
    (so also for k = h + g). `Spec.ldh_stg_ok`: under `CodesOK` the chain has `OK d`.
    `Spec.ldh_step_cnt`: under the hypotheses of its statement, at most (b + bs + bw) + L κ values
    of one round are bad (b + L κ if h = 0).
 4. A table with one row is a word. `Rename D D'`: the same code under other names (words, pairs to
    and fro); `Rename.Laws`; `Spec.ldh_rename_near`. `Rename.one C u` (rows with exactly one name),
    `Rename.pair`, `Rename.last` (the stage (0, n) with n = 0 is C.pair (Z.pair Zw)), with their
    laws.

Notation: `e`: a radius, counted in long positions (`LdCode.Near`); `LdCode.Dist d`, of a code `C`:
for all m, r not both 0, `C.T (C.enc m r)` is non-zero at d long positions or more;
`LdCode.ListAt e L`: every native word has at most L pairs (message, randomness) whose encoding is
within e long positions; `LdCode.MCAat e b`, and so at `bs`, `bw` (the agreement counts): mutual
correlated agreement on lines under the transformation, as a count of exceptional θ; `Φ`, `Φ'`: the
claims before and after the round, predicates on pairs (message, randomness) (in the counts `Φ'` is
one such for each γ); `cnt`: the number of elements of a finite type with a property
(Prob/Cnt.lean). The `LdCode` names of this paragraph are those of Cb/Ld/LdRel.lean.

Limits: counts are for one round at a time, at a fixed word and fixed claims of that round; how they
add up to an error of a protocol is the matter of the protocol's file. Lists and agreement counts
are hypotheses. This file does not say what the folds of all rounds are in closed form:
Cb/Ld/LdSumStepClosed.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSumStepStage
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Prob LdCode

/-- The bad values of a round. Φ' is the claim after the round at this γ. -/
def Halving.BadAt {E P : Type} [Field E] [Fintype P] {D D' : LdCode E P} (H : Halving D D') (e : ℕ)
    (Φ : D.MR → Prop) (Φ' : D'.MR → Prop) (f : D.Word) (γ : E) : Prop :=
  H.Exc e f γ ∨ ∃ w : D.MR, (D.Near e f (D.enc w.1 w.2) ∧ ¬ Φ w) ∧ Φ' (H.foldW γ w)

/-- A chain of halvings. -/
inductive HChain {E P : Type} : LdCode E P → LdCode E P → Type 1 where
  | nil (D : LdCode E P) : HChain D D
  | cons {D D' D'' : LdCode E P} (H : Halving D D') (t : HChain D' D'') : HChain D D''

namespace HChain
variable {E P : Type}

/-- a point: one value for each round -/
def Pt : {D D'' : LdCode E P} → HChain D D'' → Type
  | _, _, nil _ => Unit
  | _, _, cons _ t => E × t.Pt

/-- the claims: one before the first round; for each value of the first challenge, the claims of the
rest -/
def Claims : {D D'' : LdCode E P} → HChain D D'' → Type
  | D, _, nil _ => D.MR → Prop
  | D, _, cons _ t => (D.MR → Prop) × (E → t.Claims)

def first : {D D'' : LdCode E P} → (c : HChain D D'') → c.Claims → D.MR → Prop
  | _, _, nil _, cl => cl
  | _, _, cons _ _, cl => cl.1

def last : {D D'' : LdCode E P} → (c : HChain D D'') → c.Claims → c.Pt → D''.MR → Prop
  | _, _, nil _, cl, _ => cl
  | _, _, cons _ t, cl, γ => t.last (cl.2 γ.1) γ.2

variable [Field E]

def foldAll : {D D'' : LdCode E P} → (c : HChain D D'') → c.Pt → D.Word → D''.Word
  | _, _, nil _, _, f => f
  | _, _, cons H t, γ, f => t.foldAll γ.2 (H.fold γ.1 f)

def foldAllW : {D D'' : LdCode E P} → (c : HChain D D'') → c.Pt → D.MR → D''.MR
  | _, _, nil _, _, w => w
  | _, _, cons H t, γ, w => t.foldAllW γ.2 (H.foldW γ.1 w)

variable [Fintype P]

/-- The extractor of all rounds. -/
def backAll (d : ℕ) :
    {D D'' : LdCode E P} → (c : HChain D D'') → c.Pt → D.Word → D''.MR → D.MR
  | _, _, nil _, _, _, w => w
  | _, _, cons H t, γ, f, w => H.back d γ.1 f (t.backAll d γ.2 (H.fold γ.1 f) w)

def OK (d : ℕ) : {D D'' : LdCode E P} → HChain D D'' → Prop
  | _, _, nil _ => True
  | _, _, cons (D' := D') H t => D'.Laws ∧ D'.Dist d ∧ H.Laws d ∧ t.OK d

/-- some round's value is bad -/
def Bad (e : ℕ) : {D D'' : LdCode E P} → (c : HChain D D'') → c.Claims → c.Pt → D.Word → Prop
  | _, _, nil _, _, _, _ => False
  | _, _, cons H t, cl, γ, f =>
    H.BadAt e cl.1 (t.first (cl.2 γ.1)) f γ.1 ∨ t.Bad e (cl.2 γ.1) γ.2 (H.fold γ.1 f)

end HChain

/-! ## The stages -/

/-- how many variables the masks have left after k rounds -/
def endH : ℕ → ℕ → ℕ
  | 0, h => h
  | k + 1, h => endH k (h - 1)

/-- One round from the stage (k + 1, h). -/
def Halving.step {E P : Type} (C Z Zw : LdCode E P) (k : ℕ) :
    (h : ℕ) → Halving (stg C Z Zw (k + 1) h) (stg C Z Zw k (h - 1))
  | 0 => Halving.stepB C Z Zw k 0
  | h + 1 => Halving.stepA C Z Zw k h

/-- The k rounds from the stage (k, h). -/
def stgChain {E P : Type} (C Z Zw : LdCode E P) :
    (k h : ℕ) → HChain (stg C Z Zw k h) (stg C Z Zw 0 (endH k h))
  | 0, _ => HChain.nil _
  | k + 1, h => HChain.cons (Halving.step C Z Zw k h) (stgChain C Z Zw k (h - 1))

/-- a point of the chain from a function on the variables, first variable first -/
def stgPt {E P : Type} (C Z Zw : LdCode E P) : (k h : ℕ) → (Fin k → E) → (stgChain C Z Zw k h).Pt
  | 0, _, _ => ()
  | k + 1, h, γ => (γ 0, stgPt C Z Zw k (h - 1) (Fin.tail γ))

/-! ## The same code under other names -/

/-- A renaming: the data. -/
structure Rename {E P : Type} (D D' : LdCode E P) where
  word : D.Word → D'.Word
  mr : D.MR → D'.MR
  mrInv : D'.MR → D.MR

structure Rename.Laws {E P : Type} {D D' : LdCode E P} (N : Rename D D') : Prop where
  t_iff : ∀ (f g : D.Word) (x : P), D.T f x = D.T g x ↔ D'.T (N.word f) x = D'.T (N.word g) x
  enc   : ∀ w : D.MR, D'.T (N.word (D.enc w.1 w.2)) = D'.T (D'.enc (N.mr w).1 (N.mr w).2)
  left  : ∀ w, N.mrInv (N.mr w) = w
  right : ∀ w, N.mr (N.mrInv w) = w

namespace Rename
variable {E P : Type}

/-- A table whose rows have exactly one name is a word. -/
def one (C : LdCode E P) {R : Type} [Fintype R] [DecidableEq R] (u : Unique R) :
    Rename (C.il R) C where
  word f := fun p s => f p (u.default, s)
  mr w := (fun j => w.1 (u.default, j), fun q => w.2 (u.default, q))
  mrInv w := (fun j => w.1 j.2, fun q => w.2 q.2)

def pair {D₁ D₁' D₂ D₂' : LdCode E P} (N₁ : Rename D₁ D₁') (N₂ : Rename D₂ D₂') :
    Rename (D₁.pair D₂) (D₁'.pair D₂') where
  word f := mkW (N₁.word (fstW f)) (N₂.word (sndW f))
  mr w := mkM (N₁.mr (fstM w)) (N₂.mr (sndM w))
  mrInv w := mkM (N₁.mrInv (fstM w)) (N₂.mrInv (sndM w))

end Rename

/-- the cube of no variables has one corner -/
@[reducible] def uniqRows {n : ℕ} (h : n = 0) : Unique (Fin n → Bool) :=
  ⟨⟨fun _ => false⟩, fun _ => funext fun i => absurd i.2 (by omega)⟩

/-- The stage (0, n) with n = 0 under the names of C.pair (Z.pair Zw): the data. -/
def Rename.last {E P : Type} (C Z Zw : LdCode E P) {n : ℕ} (h : n = 0) :
    Rename (stg C Z Zw 0 n) (C.pair (Z.pair Zw)) :=
  (Rename.one C (uniqRows rfl)).pair ((Rename.one Z (uniqRows h)).pair (Rename.one Zw (uniqRows h)))

/-! ## The statements -/

namespace Spec
variable (E : Type) [Field E] (P : Type) [Fintype P]

def ldh_badAt_cnt [Finite E] : Prop :=
  ∀ (D D' : LdCode E P) (H : Halving D D') (e L bad κ : ℕ), D.ListAt e L →
    ∀ (Φ : D.MR → Prop) (Φ' : E → D'.MR → Prop),
      (∀ w, ¬ Φ w → cnt (fun γ => Φ' γ (H.foldW γ w)) ≤ κ) →
      ∀ f : D.Word, cnt (H.Exc e f) ≤ bad → cnt (fun γ => H.BadAt e Φ (Φ' γ) f γ) ≤ bad + L * κ

def ldh_good : Prop :=
  ∀ (D D' : LdCode E P) (H : Halving D D') (d e : ℕ), D'.Laws → D'.Dist d → H.Laws d → e < d →
    ∀ (Φ : D.MR → Prop) (Φ' : D'.MR → Prop) (f : D.Word) (γ : E), ¬ H.BadAt e Φ Φ' f γ →
      ∀ w' : D'.MR, D'.Near e (H.fold γ f) (D'.enc w'.1 w'.2) → Φ' w' →
        D.Near e f (D.enc (H.back d γ f w').1 (H.back d γ f w').2) ∧
        Φ (H.back d γ f w') ∧
        H.foldW γ (H.back d γ f w') = w'

/-- All rounds. -/
def ldh_chain : Prop :=
  ∀ (d e : ℕ), e < d →
    ∀ (D D'' : LdCode E P) (c : HChain D D''), c.OK d →
      ∀ (cl : c.Claims) (γ : c.Pt) (f : D.Word), ¬ c.Bad e cl γ f →
        ∀ w : D''.MR, D''.Near e (c.foldAll γ f) (D''.enc w.1 w.2) → c.last cl γ w →
          D.Near e f (D.enc (c.backAll d γ f w).1 (c.backAll d γ f w).2) ∧
          c.first cl (c.backAll d γ f w) ∧
          c.foldAllW γ (c.backAll d γ f w) = w

def ldh_endH : Prop := ∀ k h : ℕ, h ≤ k → endH k h = 0

def ldh_stg_ok : Prop :=
  ∀ (C Z Zw : LdCode E P) (d e : ℕ), CodesOK E P C Z Zw d e → ∀ k h, (stgChain C Z Zw k h).OK d

/-- The bad values of one round from the stage (k + 1, h). -/
def ldh_step_cnt [Finite E] : Prop :=
  ∀ (C Z Zw : LdCode E P) (k h d e L b bs bw κ : ℕ), CodesOK E P C Z Zw d e →
    (C.il (Fin k → Bool)).MCAat e b →
    (0 < h → (Z.il (Fin (h - 1) → Bool)).MCAat e bs ∧ (Zw.il (Fin (h - 1) → Bool)).MCAat e bw) →
    (stg C Z Zw (k + 1) h).ListAt e L →
    ∀ (Φ : (stg C Z Zw (k + 1) h).MR → Prop) (Φ' : E → (stg C Z Zw k (h - 1)).MR → Prop),
      (∀ w, ¬ Φ w → cnt (fun γ => Φ' γ ((Halving.step C Z Zw k h).foldW γ w)) ≤ κ) →
      ∀ f, cnt (fun γ => (Halving.step C Z Zw k h).BadAt e Φ (Φ' γ) f γ) ≤
        (b + if 0 < h then bs + bw else 0) + L * κ

def ldh_rename_near : Prop :=
  ∀ (D D' : LdCode E P) (N : Rename D D'), N.Laws → ∀ (e : ℕ) (f : D.Word) (w : D.MR),
    D.Near e f (D.enc w.1 w.2) ↔ D'.Near e (N.word f) (D'.enc (N.mr w).1 (N.mr w).2)

def ldh_one_laws : Prop :=
  ∀ (C : LdCode E P) (R : Type) [Fintype R] [DecidableEq R] (u : Unique R), (Rename.one C u).Laws
def ldh_pair_laws : Prop :=
  ∀ (D₁ D₁' D₂ D₂' : LdCode E P) (N₁ : Rename D₁ D₁') (N₂ : Rename D₂ D₂'),
    N₁.Laws → N₂.Laws → (N₁.pair N₂).Laws
def ldh_last_laws : Prop := ∀ (C Z Zw : LdCode E P) (n : ℕ) (h : n = 0), (Rename.last C Z Zw h).Laws

end Spec
end Cb
