-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSumStepCoeff.lean: the error of the round in which the verifier draws one coefficient and no
word is folded.

Definitions, a statement and its proof.

The statement of a fold holds two components, D₁ (main) and D₂ (carried mask). In the first round
the prover adds a third, W (fresh mask), and the verifier draws a coefficient. The stage
(`LdCode.stg`, Cb/Ld/LdSumStepStage.lean) after that round is D₁.pair (D₂.pair W). No word changes.

Main names:
  `LdCode.dropM w`: the pair (message, randomness) w of the three components without the part of W.
    `LdCode.dropW f`: a word f of the three components without the part of W.
  `Spec.ldk_round_coeff`: let the three components together have lists of at most L members at e,
    and let every w whose claim before the round (a claim on dropM w) is false get a true claim
    after it for at most κ values of the coefficient. Then for every word f of the three components
    and for all but L κ values: every witness after the round (a w within e of f with a true claim),
    without its part of W, is a witness before it: within e of f without the part of W (`dropW f`),
    and with a true claim.

Notation: `e`: a radius, counted in long positions (`LdCode.Near`); `LdCode.ListAt e L`: every
native word has at most L pairs (message, randomness) whose encoding is within e long positions;
`Φ`, `Φ'`: the claims before and after the round, predicates on pairs (message, randomness) (`Φ'`:
one for each value of the verifier's message); `cnt`: the number of elements of a finite type with a
property (Prob/Cnt.lean). The `LdCode` names of this paragraph are those of Cb/Ld/LdRel.lean.

Limits: the list is a hypothesis. This file does not say that κ = 1 for a claim that is affine in
the coefficient with the error of the old claim as its slope; see `lds_affine`
(Cb/Ld/LdSumStepProofs.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSumStepCx

set_option autoImplicit false

namespace Cb
open Prob LdCode

namespace LdCode
variable {E P : Type} {D₁ D₂ W : LdCode E P}

def dropM (w : (D₁.pair (D₂.pair W)).MR) : (D₁.pair D₂).MR := mkM (fstM w) (fstM (sndM w))
def dropW (f : (D₁.pair (D₂.pair W)).Word) : (D₁.pair D₂).Word := mkW (fstW f) (fstW (sndW f))

end LdCode

def Spec.ldk_round_coeff (E : Type) (P : Type) [Fintype P] [Finite E] : Prop :=
  ∀ (D₁ D₂ W : LdCode E P) (e L κ : ℕ), (D₁.pair (D₂.pair W)).ListAt e L →
    ∀ (Φ : (D₁.pair D₂).MR → Prop) (Φ' : E → (D₁.pair (D₂.pair W)).MR → Prop),
      (∀ w, ¬ Φ (dropM w) → cnt (fun ε => Φ' ε w) ≤ κ) →
      ∀ f : (D₁.pair (D₂.pair W)).Word,
        cnt (fun ε =>
            ∃ w : (D₁.pair (D₂.pair W)).MR,
              ((D₁.pair (D₂.pair W)).Near e f ((D₁.pair (D₂.pair W)).enc w.1 w.2) ∧ Φ' ε w) ∧
              ¬ ((D₁.pair D₂).Near e (dropW f) ((D₁.pair D₂).enc (dropM w).1 (dropM w).2) ∧
                Φ (dropM w))) ≤ L * κ

/-- The encoding of what is left is what is left of the encoding. -/
theorem enc_dropM {E P : Type} {D₁ D₂ W : LdCode E P} (w : (D₁.pair (D₂.pair W)).MR) :
    (D₁.pair D₂).enc (dropM w).1 (dropM w).2 = dropW ((D₁.pair (D₂.pair W)).enc w.1 w.2) := by
  funext p
  cases p <;> rfl

theorem near_drop {E P : Type} [Fintype P] {D₁ D₂ W : LdCode E P} {e : ℕ}
    {f g : (D₁.pair (D₂.pair W)).Word} (h : (D₁.pair (D₂.pair W)).Near e f g) :
    (D₁.pair D₂).Near e (dropW f) (dropW g) := by
  have key : ∀ x, (D₁.pair D₂).T (dropW f) x ≠ (D₁.pair D₂).T (dropW g) x →
      (D₁.pair (D₂.pair W)).T f x ≠ (D₁.pair (D₂.pair W)).T g x := by
    intro x hx hc
    have h1 := (t_pair_eq_iff f g x).mp hc
    have h2 := (t_pair_eq_iff (sndW f) (sndW g) x).mp h1.2
    exact hx ((t_pair_eq_iff (dropW f) (dropW g) x).mpr ⟨h1.1, h2.1⟩)
  exact le_trans (cnt_mono key) h

theorem ldk_round_coeff (E : Type) (P : Type) [Fintype P] [Finite E] :
    Spec.ldk_round_coeff E P := by
  intro D₁ D₂ W e L κ hList Φ Φ' hκ f
  refine le_trans (cnt_mono ?_)
    (lds_coeff E P (D₁.pair (D₂.pair W)) e L κ hList (fun w => Φ (dropM w)) Φ' hκ f)
  rintro ε ⟨w, ⟨hn, hc⟩, hnot⟩
  refine ⟨w, ⟨hn, hc⟩, fun hΦ => hnot ⟨?_, hΦ⟩⟩
  rw [enc_dropM]
  exact near_drop hn

end Cb
