-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSumStepCx.lean: the errors of the rounds of a fold on a complex: main rows, carried mask
rows and fresh mask rows side by side.

Definitions, statements and proofs; they use Cb/Ld/LdSumStep.lean.

The word of a round is a triple: rows under a main code C, rows under a first mask code Zs, rows
under a second mask code Zw, all read at the same long positions. There are two kinds of rounds with
a fold and one without:
  `Halving.all C Zs Zw ρ ρs ρw`: all three components are halved;
  `Halving.main C Z ρ`: only the main rows are halved, the rest Z (in its use, `Halving.stepB`,
    Cb/Ld/LdSumStepStage.lean: the pair of the two mask components) rests;
  the round of the coefficient, in which no word changes and the fresh mask is dropped by the
  extractor.

Main names (each under the hypotheses of its statement):
  `Spec.ldc_exc_pair_cnt`: the exceptional values of two halvings side by side: at most the sum of
    the two counts.
  `Spec.ldc_all_laws`, `Spec.ldc_main_laws`: the laws of the two halvings.
  `Spec.ldc_round_all`: the error of a round that halves all three: (agreement counts of the three
    codes after the round, added) + (list of the complex before the round) κ.
  `Spec.ldc_round_main`: the error of a round that halves the main rows only: (agreement count of
    the main code after the round) + (list of the complex before the round) κ.
  `Spec.ldc_round_coeff`: the round of the coefficient: (list of the complex with the fresh mask) κ;
    the witness before the round is the witness after it without the fresh mask's part, and it is
    within the same radius of the word without the fresh mask.
In all three, the "error" bounds the number of values of the verifier's message at which some
witness after the round is not taken by the extractor to a witness before it. κ is a number; by
hypothesis every w with a false claim gets a true claim after the round for at most κ values
(Cb/Ld/LdSumStep.lean, the head, 3); "(list ..) κ" is a product.

Notation: `e`: a radius, counted in long positions (`LdCode.Near`); `LdCode.Dist d`, of a code `C`:
for all m, r not both 0, `C.T (C.enc m r)` is non-zero at d long positions or more;
`LdCode.ListAt e L`: every native word has at most L pairs (message, randomness) whose encoding is
within e long positions; `LdCode.MCAat e b`, and so at `bs`, `bw` (the agreement counts): mutual
correlated agreement on lines under the transformation, as a count of exceptional θ; `Φ`, `Φ'`: the
claims before and after the round, predicates on pairs (message, randomness) (`Φ'`: one for each
value of the verifier's message); `cnt`: the number of elements of a finite type with a property
(Prob/Cnt.lean). The `LdCode` names of this paragraph are those of Cb/Ld/LdRel.lean.

Limits: what the head of Cb/Ld/LdSumStep.lean lists as not said is not said here either: lists and
agreement counts are hypotheses in the statements' text; so are the laws and the distance of the
complex after the round. One round at a time.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSumStepProofs

set_option autoImplicit false

namespace Cb
open Prob LdCode

namespace Halving
variable {E P : Type}

/-- All three components are halved. -/
def all (C Zs Zw : LdCode E P) {R R' Rs Rs' Rw Rw' : Type} [Fintype R] [DecidableEq R]
    [Fintype R'] [DecidableEq R'] [Fintype Rs] [DecidableEq Rs] [Fintype Rs'] [DecidableEq Rs']
    [Fintype Rw] [DecidableEq Rw] [Fintype Rw'] [DecidableEq Rw'] (ρ : Bool × R' ≃ R)
    (ρs : Bool × Rs' ≃ Rs) (ρw : Bool × Rw' ≃ Rw) :
    Halving ((C.il R).pair ((Zs.il Rs).pair (Zw.il Rw)))
      ((C.il R').pair ((Zs.il Rs').pair (Zw.il Rw'))) :=
  (il C ρ).pair ((il Zs ρs).pair (il Zw ρw))

/-- Only the main rows are halved. -/
def main (C Z : LdCode E P) {R R' : Type} [Fintype R] [DecidableEq R] [Fintype R']
    [DecidableEq R'] (ρ : Bool × R' ≃ R) :
    Halving ((C.il R).pair Z) ((C.il R').pair Z) :=
  (il C ρ).pair (idle Z)

end Halving

namespace Spec
variable (E : Type) [Field E] (P : Type) [Fintype P]

def ldc_exc_pair_cnt [Finite E] : Prop :=
  ∀ (D₁ D₁' D₂ D₂' : LdCode E P)
      (H₁ : Halving D₁ D₁') (H₂ : Halving D₂ D₂') (e b₁ b₂ : ℕ) (f : (D₁.pair D₂).Word),
    cnt (H₁.Exc e (fstW f)) ≤ b₁ → cnt (H₂.Exc e (sndW f)) ≤ b₂ →
    cnt ((H₁.pair H₂).Exc e f) ≤ b₁ + b₂

def ldc_all_laws : Prop :=
  ∀ (C Zs Zw : LdCode E P) (R R' Rs Rs' Rw Rw' : Type) [Fintype R] [DecidableEq R] [Fintype R']
      [DecidableEq R'] [Fintype Rs] [DecidableEq Rs] [Fintype Rs'] [DecidableEq Rs'] [Fintype Rw]
      [DecidableEq Rw] [Fintype Rw'] [DecidableEq Rw'] (ρ : Bool × R' ≃ R) (ρs : Bool × Rs' ≃ Rs)
      (ρw : Bool × Rw' ≃ Rw) (d : ℕ),
    (Halving.all C Zs Zw ρ ρs ρw).Laws d

def ldc_main_laws : Prop :=
  ∀ (C Z : LdCode E P) (R R' : Type) [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R']
      (ρ : Bool × R' ≃ R) (d : ℕ),
    Z.Laws → Z.Dist d → (Halving.main C Z ρ).Laws d

/-- A round that halves all three components. -/
def ldc_round_all [Finite E] : Prop :=
  ∀ (C Zs Zw : LdCode E P) (R R' Rs Rs' Rw Rw' : Type) [Fintype R] [DecidableEq R] [Fintype R']
      [DecidableEq R'] [Fintype Rs] [DecidableEq Rs] [Fintype Rs'] [DecidableEq Rs'] [Fintype Rw]
      [DecidableEq Rw] [Fintype Rw'] [DecidableEq Rw'] (ρ : Bool × R' ≃ R) (ρs : Bool × Rs' ≃ Rs)
      (ρw : Bool × Rw' ≃ Rw) (d e L b bs bw κ : ℕ),
    ((C.il R').pair ((Zs.il Rs').pair (Zw.il Rw'))).Laws →
    ((C.il R').pair ((Zs.il Rs').pair (Zw.il Rw'))).Dist d → e < d → (C.il R').Laws →
    (Zs.il Rs').Laws → (Zw.il Rw').Laws → (C.il R').MCAat e b → (Zs.il Rs').MCAat e bs →
    (Zw.il Rw').MCAat e bw → ((C.il R).pair ((Zs.il Rs).pair (Zw.il Rw))).ListAt e L →
    ∀ (Φ : ((C.il R).pair ((Zs.il Rs).pair (Zw.il Rw))).MR → Prop)
        (Φ' : E → ((C.il R').pair ((Zs.il Rs').pair (Zw.il Rw'))).MR → Prop),
      (∀ w, ¬ Φ w → cnt (fun γ => Φ' γ ((Halving.all C Zs Zw ρ ρs ρw).foldW γ w)) ≤ κ) →
      ∀ f, cnt (fun γ =>
          ∃ w',
            (((C.il R').pair ((Zs.il Rs').pair (Zw.il Rw'))).Near e
                ((Halving.all C Zs Zw ρ ρs ρw).fold γ f)
                (((C.il R').pair ((Zs.il Rs').pair (Zw.il Rw'))).enc w'.1 w'.2) ∧
              Φ' γ w') ∧
            ¬ (((C.il R).pair ((Zs.il Rs).pair (Zw.il Rw))).Near e f
                (((C.il R).pair ((Zs.il Rs).pair (Zw.il Rw))).enc
                  ((Halving.all C Zs Zw ρ ρs ρw).back d γ f w').1
                  ((Halving.all C Zs Zw ρ ρs ρw).back d γ f w').2) ∧
              Φ ((Halving.all C Zs Zw ρ ρs ρw).back d γ f w'))) ≤
        (b + (bs + bw)) + L * κ

/-- A round that halves the main rows only. -/
def ldc_round_main [Finite E] : Prop :=
  ∀ (C Z : LdCode E P) (R R' : Type) [Fintype R] [DecidableEq R] [Fintype R'] [DecidableEq R']
      (ρ : Bool × R' ≃ R) (d e L b κ : ℕ),
    ((C.il R').pair Z).Laws → ((C.il R').pair Z).Dist d → e < d → (C.il R').Laws →
    Z.Laws → Z.Dist d → (C.il R').MCAat e b → ((C.il R).pair Z).ListAt e L →
    ∀ (Φ : ((C.il R).pair Z).MR → Prop) (Φ' : E → ((C.il R').pair Z).MR → Prop),
      (∀ w, ¬ Φ w → cnt (fun γ => Φ' γ ((Halving.main C Z ρ).foldW γ w)) ≤ κ) →
      ∀ f, cnt (fun γ =>
          ∃ w',
            (((C.il R').pair Z).Near e ((Halving.main C Z ρ).fold γ f)
                (((C.il R').pair Z).enc w'.1 w'.2) ∧
              Φ' γ w') ∧
            ¬ (((C.il R).pair Z).Near e f
                (((C.il R).pair Z).enc ((Halving.main C Z ρ).back d γ f w').1
                  ((Halving.main C Z ρ).back d γ f w').2) ∧
              Φ ((Halving.main C Z ρ).back d γ f w'))) ≤ b + L * κ

/-- The round of the coefficient. D: what the statement holds (main and carried mask); W: the fresh
mask. The extractor drops the part of W. -/
def ldc_round_coeff [Finite E] : Prop :=
  ∀ (D W : LdCode E P) (e L κ : ℕ), (D.pair W).ListAt e L →
    ∀ (Φ : D.MR → Prop) (Φ' : E → (D.pair W).MR → Prop),
      (∀ w, ¬ Φ (fstM w) → cnt (fun ε => Φ' ε w) ≤ κ) →
      ∀ f : (D.pair W).Word,
        cnt (fun ε =>
            ∃ w : (D.pair W).MR,
              ((D.pair W).Near e f ((D.pair W).enc w.1 w.2) ∧ Φ' ε w) ∧
              ¬ (D.Near e (fstW f) (D.enc (fstM w).1 (fstM w).2) ∧ Φ (fstM w))) ≤ L * κ

end Spec

section
variable (E : Type) [Field E] (P : Type) [Fintype P]

theorem ldc_exc_pair_cnt [Finite E] : Spec.ldc_exc_pair_cnt E P := by
  intro D₁ D₁' D₂ D₂' H₁ H₂ e b₁ b₂ f h₁ h₂
  cases nonempty_fintype E
  exact (cnt_le_add fun γ hγ => lds_exc_pair E P D₁ D₁' D₂ D₂' H₁ H₂ e f γ hγ).trans
    (Nat.add_le_add h₁ h₂)

omit [Field E] in
theorem ldc_all_laws :
    Spec.ldc_all_laws E P := fun C Zs Zw R R' Rs Rs' Rw Rw' _ _ _ _ _ _ _ _ _ _ _ _ ρ ρs ρw d =>
  lds_pair_laws E P _ _ _ _ _ _ d (lds_il_laws E P C R R' ρ d)
    (lds_pair_laws E P _ _ _ _ _ _ d (lds_il_laws E P Zs Rs Rs' ρs d)
      (lds_il_laws E P Zw Rw Rw' ρw d))

theorem ldc_main_laws : Spec.ldc_main_laws E P := fun C Z R R' _ _ _ _ ρ d hL hd =>
  lds_pair_laws E P _ _ _ _ _ _ d (lds_il_laws E P C R R' ρ d) (lds_idle_laws E P Z d hL hd)

theorem ldc_round_all [Finite E] : Spec.ldc_round_all E P := by
  intro C Zs Zw R R' Rs Rs' Rw Rw' _ _ _ _ _ _ _ _ _ _ _ _ ρ ρs ρw d e L b bs bw κ hL hd he hLC hLs
    hLw hb hbs hbw hList Φ Φ' hκ f
  refine lds_round E P _ _ (Halving.all C Zs Zw ρ ρs ρw) d e L (b + (bs + bw)) κ hL hd
    (ldc_all_laws E P C Zs Zw R R' Rs Rs' Rw Rw' ρ ρs ρw d) he hList Φ Φ' hκ f ?_
  refine ldc_exc_pair_cnt E P _ _ _ _ (Halving.il C ρ) ((Halving.il Zs ρs).pair (Halving.il Zw ρw))
    e b (bs + bw) f (lds_exc_cnt E P _ _ _ e b hLC hb _) ?_
  exact ldc_exc_pair_cnt E P _ _ _ _ (Halving.il Zs ρs) (Halving.il Zw ρw) e bs bw _
    (lds_exc_cnt E P _ _ _ e bs hLs hbs _) (lds_exc_cnt E P _ _ _ e bw hLw hbw _)

theorem ldc_round_main [Finite E] : Spec.ldc_round_main E P := by
  intro C Z R R' _ _ _ _ ρ d e L b κ hL hd he hLC hLZ hdZ hb hList Φ Φ' hκ f
  refine lds_round E P _ _ (Halving.main C Z ρ) d e L b κ hL hd
    (ldc_main_laws E P C Z R R' ρ d hLZ hdZ) he hList Φ Φ' hκ f ?_
  have h := ldc_exc_pair_cnt E P _ _ _ _ (Halving.il C ρ) (Halving.idle Z) e b 0 f
    (lds_exc_cnt E P _ _ _ e b hLC hb _) (le_of_eq (cnt_false fun γ => lds_exc_idle E P Z e _ γ))
  rwa [Nat.add_zero] at h

omit [Field E] in
theorem near_fst {E P : Type} [Fintype P] {D W : LdCode E P} {e : ℕ}
    {f g : (D.pair W).Word} (h : (D.pair W).Near e f g) : D.Near e (fstW f) (fstW g) :=
  le_trans (cnt_mono fun x hx hc => hx ((t_pair_eq_iff f g x).mp hc).1) h

omit [Field E] in
theorem ldc_round_coeff [Finite E] : Spec.ldc_round_coeff E P := by
  intro D W e L κ hList Φ Φ' hκ f
  refine le_trans (cnt_mono ?_) (lds_coeff E P (D.pair W) e L κ hList (fun w => Φ (fstM w)) Φ' hκ f)
  rintro ε ⟨w, ⟨hn, hc⟩, hnot⟩
  exact ⟨w, ⟨hn, hc⟩, fun hΦ => hnot ⟨near_fst hn, hΦ⟩⟩

end
end Cb
