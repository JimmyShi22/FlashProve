-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSumStep.lean: one round in which a word is folded, at any radius below the distance, so also
beyond unique decoding: its extractor and its error, stated on words.

Definitions and statements (each a `Prop` in `Cb.Spec`); the proofs are in
Cb/Ld/LdSumStepProofs.lean. No protocol term is in this file: words, (message, randomness) pairs,
and counts of values of one verifier message.

The round. D is the code before the round, D' the code after it (`LdCode`, Cb/Ld/LdRel.lean, read at
the same long positions). A word f of D has two halves, lo f and hi f, words of D'. The verifier
draws γ, and the word after the round is the fold (1 - γ) lo f + γ hi f.
A claim Φ on (message, randomness) of D stands before the round, a claim Φ' γ on those of D' after
it. Beyond half the distance f has no decoding; the relaxed relations (`ConL`, Cb/Ld/LdRel.lean) say
"some (message, randomness) has an encoding within e long positions of the word, and meets the
claim".
The extractor runs backwards (`H.back`): from a pair w' for the word after the round it takes the
set S of long positions at which the fold agrees with the encoding of w', corrects the erasures of
both halves on S (Cb/Gen/CodeEraseLd.lean), and joins the two results.

Main names:
 1. `Halving D D'`: the data. `Halving.Laws d`. `H.fold`, `H.foldW`, `H.back`, `H.Exc` (γ is
    exceptional for the two halves of f: `LdCode.ExcFold`, Cb/Gen/CodeEraseLd.lean; see "agreement"
    in the terms).
 2. `Spec.lds_back`, the backward step: under `D'.Laws`, `D'.Dist d` and `H.Laws d`, if e < d and γ
    is not exceptional, then for every w' whose encoding is within e of the fold, w = H.back .. w'
    has an encoding within e of f, and w folds to w' at γ.
 3. `Spec.lds_round`, the round's error: under the same three hypotheses and e < d, let D have lists
    of at most L members at e, let at most "bad" values be exceptional, and let every w with a false
    claim get a true claim after the round for at most κ values of γ. Then for all but bad + L κ
    values of γ: every witness after the round is taken by `H.back` to a witness before it. The list
    is that of the code before the round. `Spec.lds_poly`: κ = d - 1 for a sumcheck round with
    polynomials of degree below d whose sums over {0, 1} differ (there d is a bound on the degrees,
    not the distance).
 4. The instances. `Halving.il C ρ`: rows R of an interleaved code, split by ρ : Bool × R' ≃ R (any
    order of folding). `Halving.pair`. `Halving.idle Z`: a code that the round leaves alone (both
    halves are the word itself; the fold is the word). Their laws: `Spec.lds_il_laws`;
    `Spec.lds_pair_laws`, from the laws of both; `Spec.lds_idle_laws`, under `Z.Laws` and
    `Z.Dist d`. The exceptional values: those of a pair are exceptional for one of the sides
    (`Spec.lds_exc_pair`), an idle code has none (`Spec.lds_exc_idle`). So the agreement errors add
    over the components that are halved, and a component that rests costs nothing.
 5. A round without a fold (a coefficient is drawn, the words stay): `Spec.lds_coeff`: with L and κ
    as in 3 (no other hypothesis), for all but L κ values every witness after the round is a witness
    before it; `Spec.lds_affine`: κ = 1 for a claim that is affine in the coefficient, with a
    non-zero slope.

Limits:
One difference, a narrowing, is declared. The paper that this protocol builds on (lean/CREDITS.md)
asks only that the radius be below the distance of what is READ of the code, so a transformation may
forget a part of a codeword; its extractor then adds one more correction to both halves, so that
they fold exactly to the given pair.
Here `D'.Dist d` with `D'.Laws` and d ≥ 1 (from e < d) says that what is read determines (message,
randomness); that correction is then 0, and it is not written. Reading as it stands, repetition, and
multiples by non-zero scalars are transformations of this kind.
The values γ are counted in all of E; a count over a smaller set of challenges is no larger.
No bound on lists or on exceptional values is proved or assumed: they are hypotheses in the
statements' own text; two statements are excepted: `Spec.lds_exc_idle` (an idle code's exceptional
values: none) and `Spec.lds_exc_cnt` (the number of exceptional values, under `D'.Laws`, from the
hypothesis `D'.MCAat e bad`). This file says nothing for an exceptional γ. It says nothing on
several rounds, on the honest prover, on zero knowledge, on running time. That D' has its laws and
its distance is a hypothesis. For pairs and interleavings Cb/Ld/LdRel.lean states it from those of
the parts.

Terms: lean/GLOSSARY.md.
-/
import Alg.Poly
import Cb.Gen.CodeEraseLdProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Prob

/-- A halving: the data. D before the round, D' after it. -/
structure Halving {E P : Type} (D D' : LdCode E P) where
  /-- the two halves of a word -/
  lo : D.Word → D'.Word
  hi : D.Word → D'.Word
  /-- the two halves of (message, randomness) -/
  loW : D.MR → D'.MR
  hiW : D.MR → D'.MR
  /-- from the halves back -/
  join : D'.MR → D'.MR → D.MR
  /-- these two are the halves of one -/
  Fit : D'.MR → D'.MR → Prop

namespace Halving
variable {E P : Type} [Field E] {D D' : LdCode E P} (H : Halving D D')

/-- The laws of a halving; d is a number at or below the distance of D' (`D'.Dist d`, in the
statements). Only what is read of a word (its transform) enters. -/
structure Laws [Fintype P] (d : ℕ) : Prop where
  /-- the halves of an encoding are the encodings of the halves -/
  enc_lo : ∀ w : D.MR, D'.T (H.lo (D.enc w.1 w.2)) = D'.T (D'.enc (H.loW w).1 (H.loW w).2)
  enc_hi : ∀ w : D.MR, D'.T (H.hi (D.enc w.1 w.2)) = D'.T (D'.enc (H.hiW w).1 (H.hiW w).2)
  /-- two words are read alike at a long position if and only if both their halves are -/
  t_iff  : ∀ (f g : D.Word) (x : P),
    D.T f x = D.T g x ↔ D'.T (H.lo f) x = D'.T (H.lo g) x ∧ D'.T (H.hi f) x = D'.T (H.hi g) x
  lo_join : ∀ w₀ w₁, H.Fit w₀ w₁ → H.loW (H.join w₀ w₁) = w₀
  hi_join : ∀ w₀ w₁, H.Fit w₀ w₁ → H.hiW (H.join w₀ w₁) = w₁
  /-- what fits the two halves of one word on a common large set are the halves of one -/
  fit : ∀ (f : D.Word) (S : Finset P) (w₀ w₁ : D'.MR), Fintype.card P < S.card + d →
    D'.AgreesOn S (D'.T (H.lo f)) w₀ → D'.AgreesOn S (D'.T (H.hi f)) w₁ → H.Fit w₀ w₁

/-- The fold of a word, and of (message, randomness). -/
def fold (γ : E) (f : D.Word) : D'.Word := (1 - γ) • H.lo f + γ • H.hi f
def foldW (γ : E) (w : D.MR) : D'.MR := (1 - γ) • H.loW w + γ • H.hiW w

variable [Fintype P]

/-- The backward extractor of the round. -/
def back (d : ℕ) (γ : E) (f : D.Word) (w' : D'.MR) : D.MR :=
  H.join (D'.eraseD d (D'.agr (D'.T (H.fold γ f)) w') (D'.T (H.lo f)))
    (D'.eraseD d (D'.agr (D'.T (H.fold γ f)) w') (D'.T (H.hi f)))

/-- γ is exceptional for the two halves of f at the radius e. -/
def Exc (e : ℕ) (f : D.Word) (γ : E) : Prop := D'.ExcFold e (H.lo f) (H.hi f) γ

end Halving

/-! ## The instances -/

namespace LdCode
variable {E P : Type} {C₁ C₂ : LdCode E P}

/-- the two sides of (message, randomness) of a pair, and back -/
def fstM (w : (C₁.pair C₂).MR) : C₁.MR := (fun j => w.1 (.inl j), fun q => w.2 (.inl q))
def sndM (w : (C₁.pair C₂).MR) : C₂.MR := (fun j => w.1 (.inr j), fun q => w.2 (.inr q))
def mkM (w₁ : C₁.MR) (w₂ : C₂.MR) : (C₁.pair C₂).MR := (Sum.elim w₁.1 w₂.1, Sum.elim w₁.2 w₂.2)

end LdCode

namespace Halving
variable {E P : Type}

/-- Rows of an interleaved code, split in two by ρ. -/
def il (C : LdCode E P) {R R' : Type} [Fintype R] [DecidableEq R] [Fintype R']
    [DecidableEq R'] (ρ : Bool × R' ≃ R) : Halving (C.il R) (C.il R') where
  lo f := fun p s => f p (ρ (false, s.1), s.2)
  hi f := fun p s => f p (ρ (true, s.1), s.2)
  loW w := (fun j => w.1 (ρ (false, j.1), j.2), fun q => w.2 (ρ (false, q.1), q.2))
  hiW w := (fun j => w.1 (ρ (true, j.1), j.2), fun q => w.2 (ρ (true, q.1), q.2))
  join w₀ w₁ := (fun j =>
      cond (ρ.symm j.1).1 (w₁.1 ((ρ.symm j.1).2, j.2)) (w₀.1 ((ρ.symm j.1).2, j.2)),
    fun q => cond (ρ.symm q.1).1 (w₁.2 ((ρ.symm q.1).2, q.2)) (w₀.2 ((ρ.symm q.1).2, q.2)))
  Fit _ _ := True

/-- Two halvings side by side. -/
def pair {D₁ D₁' D₂ D₂' : LdCode E P} (H₁ : Halving D₁ D₁') (H₂ : Halving D₂ D₂') :
    Halving (D₁.pair D₂) (D₁'.pair D₂') where
  lo f := LdCode.mkW (H₁.lo (LdCode.fstW f)) (H₂.lo (LdCode.sndW f))
  hi f := LdCode.mkW (H₁.hi (LdCode.fstW f)) (H₂.hi (LdCode.sndW f))
  loW w := LdCode.mkM (H₁.loW (LdCode.fstM w)) (H₂.loW (LdCode.sndM w))
  hiW w := LdCode.mkM (H₁.hiW (LdCode.fstM w)) (H₂.hiW (LdCode.sndM w))
  join w₀ w₁ := LdCode.mkM (H₁.join (LdCode.fstM w₀) (LdCode.fstM w₁))
    (H₂.join (LdCode.sndM w₀) (LdCode.sndM w₁))
  Fit w₀ w₁ := H₁.Fit (LdCode.fstM w₀) (LdCode.fstM w₁) ∧ H₂.Fit (LdCode.sndM w₀) (LdCode.sndM w₁)

/-- A code that the round leaves alone. -/
def idle (Z : LdCode E P) : Halving Z Z where
  lo f := f
  hi f := f
  loW w := w
  hiW w := w
  join w₀ _ := w₀
  Fit w₀ w₁ := w₀ = w₁

end Halving

/-! ## The statements -/

namespace Spec
variable (E : Type) [Field E] (P : Type) [Fintype P]

/-- The backward step. -/
def lds_back : Prop :=
  ∀ (D D' : LdCode E P) (H : Halving D D') (d e : ℕ), D'.Laws → D'.Dist d → H.Laws d → e < d →
    ∀ (f : D.Word) (γ : E), ¬ H.Exc e f γ →
      ∀ w' : D'.MR, D'.Near e (H.fold γ f) (D'.enc w'.1 w'.2) →
        D.Near e f (D.enc (H.back d γ f w').1 (H.back d γ f w').2) ∧
        H.foldW γ (H.back d γ f w') = w'

/-- The union bound over a list: if each member spoils at most κ values, the list spoils at most
(its size) κ. -/
def lds_cnt_list : Prop :=
  ∀ (α β : Type) [Finite α] [Finite β] (Pm : β → Prop) (Q : β → α → Prop) (L κ : ℕ),
    cnt Pm ≤ L → (∀ b, Pm b → cnt (Q b) ≤ κ) → cnt (fun a => ∃ b, Pm b ∧ Q b a) ≤ L * κ

/-- The error of the round. -/
def lds_round [Finite E] : Prop :=
  ∀ (D D' : LdCode E P) (H : Halving D D') (d e L bad κ : ℕ), D'.Laws → D'.Dist d →
    H.Laws d → e < d → D.ListAt e L →
    ∀ (Φ : D.MR → Prop) (Φ' : E → D'.MR → Prop),
      (∀ w, ¬ Φ w → cnt (fun γ => Φ' γ (H.foldW γ w)) ≤ κ) →
      ∀ f : D.Word, cnt (H.Exc e f) ≤ bad →
        cnt (fun γ =>
            ∃ w' : D'.MR,
              (D'.Near e (H.fold γ f) (D'.enc w'.1 w'.2) ∧ Φ' γ w') ∧
              ¬ (D.Near e f (D.enc (H.back d γ f w').1 (H.back d γ f w').2) ∧
                Φ (H.back d γ f w'))) ≤ bad + L * κ

/-- A sumcheck round: the member's own polynomial p and the prover's q have degree below d; if their
sums over {0, 1} differ, they agree at no more than d - 1 values. -/
def lds_poly [Finite E] : Prop :=
  ∀ (d : ℕ) (p q : Polynomial E), p.natDegree < d → q.natDegree < d →
    p.eval 0 + p.eval 1 ≠ q.eval 0 + q.eval 1 → cnt (fun γ : E => p.eval γ = q.eval γ) ≤ d - 1

def lds_il_laws : Prop :=
  ∀ (C : LdCode E P) (R R' : Type) [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R']
      (ρ : Bool × R' ≃ R) (d : ℕ),
    (Halving.il C ρ).Laws d

def lds_pair_laws : Prop :=
  ∀ (D₁ D₁' D₂ D₂' : LdCode E P) (H₁ : Halving D₁ D₁') (H₂ : Halving D₂ D₂') (d : ℕ),
    H₁.Laws d → H₂.Laws d → (H₁.pair H₂).Laws d

def lds_idle_laws : Prop := ∀ (Z : LdCode E P) (d : ℕ), Z.Laws → Z.Dist d → (Halving.idle Z).Laws d

/-- An exceptional value of a pair is exceptional for one of the sides. -/
def lds_exc_pair : Prop :=
  ∀ (D₁ D₁' D₂ D₂' : LdCode E P)
      (H₁ : Halving D₁ D₁') (H₂ : Halving D₂ D₂') (e : ℕ) (f : (D₁.pair D₂).Word) (γ : E),
    (H₁.pair H₂).Exc e f γ → H₁.Exc e (LdCode.fstW f) γ ∨ H₂.Exc e (LdCode.sndW f) γ

/-- A code that rests has no exceptional value. -/
def lds_exc_idle : Prop :=
  ∀ (Z : LdCode E P) (e : ℕ) (f : Z.Word) (γ : E), ¬ (Halving.idle Z).Exc e f γ

/-- States: under `D'.Laws` and `D'.MCAat e bad`, at most bad values are exceptional for the two
halves of any word f. -/
def lds_exc_cnt [Finite E] : Prop :=
  ∀ (D D' : LdCode E P) (H : Halving D D') (e bad : ℕ),
    D'.Laws → D'.MCAat e bad → ∀ f : D.Word, cnt (H.Exc e f) ≤ bad

/-- A round without a fold. -/
def lds_coeff [Finite E] : Prop :=
  ∀ (D : LdCode E P) (e L κ : ℕ), D.ListAt e L →
    ∀ (Φ : D.MR → Prop) (Φ' : E → D.MR → Prop), (∀ w, ¬ Φ w → cnt (fun ε => Φ' ε w) ≤ κ) →
      ∀ f : D.Word, cnt (fun ε => ∃ w : D.MR, (D.Near e f (D.enc w.1 w.2) ∧ Φ' ε w) ∧ ¬ Φ w) ≤ L * κ

/-- A claim that is affine in the coefficient, with a non-zero slope, holds for at most one
value. -/
def lds_affine [Finite E] : Prop := ∀ a b : E, a ≠ 0 → cnt (fun ε : E => ε * a + b = 0) ≤ 1

end Spec
end Cb
