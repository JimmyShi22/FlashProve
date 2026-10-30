-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageQChain.lean: the code of a round's message for the chain's data, and the leaves' code, of
the encoding of the queries (Run/CodingPage.lean: `PageC`) at the generic construction
(Run/PlanQS.lean): by recursion on the rounds' data.

The compiled verifier asks typed oracles (`OracleName`, Compile/Batch/Oracles.lean), among them those for
chain queries and for the leaves and nodes of hash trees. To run it over one hash function, every
typed query, with the number of a block of its answer, is written as a bit string by a one-to-one
encoding with a parser (a coding: `Rom.OracleCoding`, Rom/Family.lean). Run/CodingPage.lean builds such an
encoding from a record of data, `PageC`.
This file makes what two fields of that record (`chain`, `leafP`) need at the protocols that
Run/PlanQS.lean builds from a description: the code of each round's prover message in a chain
query, and the code of a hash tree's leaf. Definitions that compute, with their laws. After the
format page, in an edition that is not the one that ships: R5.2, R8.2 (a
round's message), R7.1, R7.3, R7.4 (a column, a leaf's bytes, its
label).
A partial code (`PCode A`, Run/CodingPart.lean) writes some points of A as bit strings (`put`) and
reads them back (`parse`); its two laws: `parse s = some a` exactly if `put a = some s`.

Why: no round, shape (`Iop.Shape`; `Fmt.Shape`, a tree's numbers, is data), protocol or interface
is a parameter (shapes stand in types alone). That is this folder's principle for what stands on a
run's path; the head of Run/PlanQS.lean tells the reason.

Main names:
  `PBL C ds`: the type of a plain part of some round after the trivial round (`s0`,
    Run/PlanQS.lean).
  `rcL C ds i`: the partial code of (root or none, plain part) at the round with the number i in ds
    (from 0): the plain part must be that round's slot part; it writes Run/PageQMsg.lean's
    `pRound`; a number beyond ds: nothing; `rcL_ge`: at least 64 bits.
  `leafCL C salt ds`: the partial code of a symbol with its position: the word (leaves' number:
    `t164`, Run/CodingTag.lean) + 2^16 (tree's number) + 2^32 (the number of the column's words) +
    2^56 (the number of the salt's words) (the format page, in an edition that is not the one
    that ships: R2.1, R7.3, R7.4); the word 2^depth + position; the column; the fill's zero
    bytes.
  `tagsOK salt ds`: a test, to be evaluated at a closed description: for each round (one without a
    tree counts with the numbers 0), the word with the tree's number has the leaves' number in its
    low 16 bits; `leafCL_tag`: then every string begins with these 16 bits.

Limits: this file does not say that the strings are those of Run/PlanQS.lean's spellings (`msgSL`,
`nonceSL`, `leafSL`): another file's tie.

Terms: lean/GLOSSARY.md.
-/
import Run.PageQMsg
import Run.PlanQS
import Run.CodingTag
import Run.ToyCode

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch

/-- a plain part of some round after the trivial round -/
abbrev PBL (C : CK) (ds : List RD) : Type := PlainPart (uL C ds) (RoundSplits.allLocal (uL C ds))

section
variable {R A B : Type}

/-- the left summand, beside a first component -/
def selInl (x : R × (A ⊕ B)) : Option (R × A) :=
  match x.2 with
  | .inl a => some (x.1, a)
  | .inr _ => none

def selInr (x : R × (A ⊕ B)) : Option (R × B) :=
  match x.2 with
  | .inl _ => none
  | .inr b => some (x.1, b)

theorem selInl_mk (y : R × A) : selInl (B := B) (y.1, .inl y.2) = some y := rfl
theorem selInr_mk (y : R × B) : selInr (A := A) (y.1, .inr y.2) = some y := rfl

theorem mk_selInl (x : R × (A ⊕ B)) (y : R × A) (h : selInl x = some y) :
    ((y.1, .inl y.2) : R × (A ⊕ B)) = x := by
  obtain ⟨r, a | b⟩ := x
  · rw [← Option.some.inj h]
  · cases h

theorem mk_selInr (x : R × (A ⊕ B)) (y : R × B) (h : selInr x = some y) :
    ((y.1, .inr y.2) : R × (A ⊕ B)) = x := by
  obtain ⟨r, a | b⟩ := x
  · cases h
  · rw [← Option.some.inj h]

/-- a partial code carried into the left summand -/
def inL (p : PCode (R × A)) : PCode (R × (A ⊕ B)) :=
  p.via selInl (fun y => (y.1, .inl y.2)) selInl_mk mk_selInl

/-- a partial code carried into the right summand -/
def inR (p : PCode (R × B)) : PCode (R × (A ⊕ B)) :=
  p.via selInr (fun y => (y.1, .inr y.2)) selInr_mk mk_selInr

theorem inL_put (p : PCode (R × A)) (x : R × (A ⊕ B)) (s : List Bool) (h : (inL p).put x = some s) :
    ∃ y, p.put y = some s := by
  obtain ⟨y, -, hy⟩ := PCode.via_put' _ _ _ _ _ x s h
  exact ⟨y, hy⟩

theorem inR_put (p : PCode (R × B)) (x : R × (A ⊕ B)) (s : List Bool) (h : (inR p).put x = some s) :
    ∃ y, p.put y = some s := by
  obtain ⟨y, -, hy⟩ := PCode.via_put' _ _ _ _ _ x s h
  exact ⟨y, hy⟩

end

/-- A round's message, at the round with the number i. -/
def rcL (C : CK) : (ds : List RD) → ℕ → PCode (Option (Dig 256) × PBL C ds)
  | [], _ => PCode.empty _
  | d :: _, 0 => inL (inR (pRound d.entry.work d.items))
  | _ :: ds, i + 1 => inR (rcL C ds i)

theorem rcL_ge (C : CK) :
    ∀ (ds : List RD) (i : ℕ) (y : Option (Dig 256) × PBL C ds) (s : List Bool),
      (rcL C ds i).put y = some s → 64 ≤ s.length
  | [], _, _, _, h => by cases h
  | d :: _, 0, y, s, h => by
      obtain ⟨y1, h1⟩ := inL_put _ y s h
      obtain ⟨y2, h2⟩ := inR_put _ y1 s h1
      rw [pRound_len d.entry.work d.items y2 s h2]
      omega
  | _ :: ds, i + 1, y, s, h => by
      obtain ⟨y1, h1⟩ := inR_put _ y s h
      exact rcL_ge C ds i y1 s h1

/-! ### Leaves -/

end Run.PQ

namespace Run.PCode
variable {A B : Type}

/-- On a sum, with no condition: a point of the right summand is written only if its string is none
of the left code's. -/
def sumF (p : PCode A) (q : PCode B) : PCode (A ⊕ B) where
  put := fun x => match x with
    | .inl a => p.put a
    | .inr b => (q.put b).filter fun s => (p.parse s).isNone
  parse := fun s => match p.parse s with
    | some a => some (.inl a)
    | none => (q.parse s).map .inr
  parse_put := fun x s hx => by
    rcases x with a | b
    · have := p.parse_put a s hx
      simp [this]
    · obtain ⟨h1, h2⟩ := Option.filter_eq_some_iff.1 hx
      have h3 : p.parse s = none := Option.isNone_iff_eq_none.1 h2
      have := q.parse_put b s h1
      simp [h3, this]
  put_parse := fun s x hx => by
    cases hp : p.parse s with
    | some a =>
        simp only [hp] at hx
        rw [← Option.some.inj hx]
        exact p.put_parse s a hp
    | none =>
        simp only [hp] at hx
        cases hq : q.parse s with
        | none => rw [hq] at hx; cases hx
        | some b =>
            rw [hq] at hx
            rw [← Option.some.inj hx]
            show (q.put b).filter (fun s => (p.parse s).isNone) = some s
            rw [q.put_parse s b hq]
            simp [hp]

theorem sumF_inr (p : PCode A) (q : PCode B) (b : B) (s : List Bool)
    (h : (p.sumF q).put (.inr b) = some s) : q.put b = some s :=
  (Option.filter_eq_some_iff.1 h).1

end Run.PCode

namespace Run.PQ
open Rom Iop Compile Compile.Batch

/-- A column of W words, with the length of its strings. -/
def pVec : (W : ℕ) → { p : PCode (Fin W → UInt64) // p.Len (64 * W) }
  | 0 =>
    ⟨(pUnit []).congr
        ⟨fun _ i => i.elim0, fun _ => (), fun _ => rfl, fun _ => funext fun i => i.elim0⟩,
      fun _ s h => by rw [← Option.some.inj h]; rfl⟩
  | W + 1 => ⟨(pU64.cons 64 pU64_len fun _ => (pVec W).1).congr
      (Fin.consEquiv fun _ : Fin (W + 1) => UInt64),
      fun b s h => by
        have := PCode.congr_len _ (Fin.consEquiv fun _ : Fin (W + 1) => UInt64) _
          (PCode.cons_len pU64 64 pU64_len (fun _ => (pVec W).1) (64 * W) fun _ => (pVec W).2) b s h
        omega⟩

/-- the label's first word: the leaves' number; above it the tree's number, the number of the
column's words and the number of the salt's words (Fmt/Rules23.lean: leafPlace) -/
def leafWord (t : Option _root_.Fmt.Shape) (salt : ℕ) : List Bool :=
  bytesToBits (_root_.Fmt.u64n (164 + 65536 * _root_.Fmt.leafPlace (trNo t) (colW t) (salt / 8)))

/-- the fill, as bits -/
def fillBits (t : Option _root_.Fmt.Shape) (salt : ℕ) : List Bool :=
  bytesToBits (_root_.Fmt.zeroBytes (_root_.Fmt.fillLen (colW t) salt))

/-- the leaves of one tree: position and column -/
def leaf1 (t : Option _root_.Fmt.Shape) (salt : ℕ) :
    PCode (Fin (posN t) × (Fin (colW t) → UInt64)) :=
  (PCode.pre (leafWord t salt)
      ((pFinAt (posN t) (posN t)).cons 64 (pFinAt_len _ _) fun _ =>
        (pVec (colW t)).1.cons (64 * colW t) (pVec (colW t)).2 fun _ =>
          pUnit (fillBits t salt))).congr
    ⟨fun x => (x.1, x.2.1), fun y => (y.1, (y.2, ())), fun _ => rfl, fun _ => rfl⟩

theorem leaf1_pre (t : Option _root_.Fmt.Shape) (salt : ℕ)
    (y : Fin (posN t) × (Fin (colW t) → UInt64))
    (m : List Bool) (h : (leaf1 t salt).put y = some m) : ∃ r, m = leafWord t salt ++ r :=
  PCode.pre_put _ _ _ m h

/-- A symbol with its position. A later round's leaf is written only if its string is none of an
earlier round's: so this is a code whatever the trees' numbers are. -/
def leafCL (C : CK) (salt : ℕ) : (ds : List RD) → PCode (SymAny (uL C ds))
  | [] => PCode.empty _
  | d :: ds =>
    (((leaf1 d.tree salt).congr (Equiv.sigmaEquivProd _ _).symm).sumF (leafCL C salt ds)).congr
      (Equiv.sumSigmaDistrib (α := Fin (posN d.tree))
        (β := OPos (uL C ds)) (OSym (uL C (d :: ds)))).symm

/-- A test: the word with a tree's number has the leaves' number in its low 16 bits. -/
def tagsOK (salt : ℕ) : List RD → Bool
  | [] => true
  | d :: ds => decide ((leafWord d.tree salt).take 16 = t164) && tagsOK salt ds

theorem leafCL_tag (C : CK) (salt : ℕ) :
    ∀ (ds : List RD), tagsOK salt ds = true →
      ∀ (y : SymAny (uL C ds)) (m : List Bool),
        (leafCL C salt ds).put y = some m → 16 ≤ m.length ∧ m.take 16 = t164
  | [], _, _, _, h => by cases h
  | d :: ds, hk, y, m, h => by
      have hk' : (decide ((leafWord d.tree salt).take 16 = t164) && tagsOK salt ds) = true := hk
      rw [Bool.and_eq_true, decide_eq_true_iff] at hk'
      rcases hz : (Equiv.sumSigmaDistrib
          (α := Fin (posN d.tree)) (β := OPos (uL C ds)) (OSym (uL C (d :: ds)))) y with a | b
      · have h1 : (leaf1 d.tree salt).put ((Equiv.sigmaEquivProd _ _) a) = some m := by
          have h0 : (((leaf1 d.tree salt).congr (Equiv.sigmaEquivProd _ _).symm).sumF
                  (leafCL C salt ds)).put
                ((Equiv.sumSigmaDistrib (α := Fin (posN d.tree))
                  (β := OPos (uL C ds)) (OSym (uL C (d :: ds)))) y) = some m := h
          rw [hz] at h0
          exact h0
        obtain ⟨r, rfl⟩ := leaf1_pre d.tree salt _ m h1
        have hl : (leafWord d.tree salt).length = 64 := length_u64n _
        exact ⟨by rw [List.length_append, hl]; omega, (take16 _ r (by rw [hl]; omega)).trans hk'.1⟩
      · have h0 : (((leaf1 d.tree salt).congr (Equiv.sigmaEquivProd _ _).symm).sumF
                (leafCL C salt ds)).put
              ((Equiv.sumSigmaDistrib (α := Fin (posN d.tree))
                (β := OPos (uL C ds)) (OSym (uL C (d :: ds)))) y) = some m := h
        rw [hz] at h0
        exact leafCL_tag C salt ds hk'.2 b m (PCode.sumF_inr _ _ b m h0)

end Run.PQ
