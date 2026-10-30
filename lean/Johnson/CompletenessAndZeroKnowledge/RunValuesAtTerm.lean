-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/RunValuesAtTerm.lean: the chance that a coin's run value falls in a set.

1.  A coin of the honest provers is purses and two run values: the chance that a run value lies in a set is that of its own coordinate.
2.  This file claims nothing of a protocol: this file proves neither completeness nor zero knowledge of the protocol.
-/
import Johnson.CompletenessAndZeroKnowledge.FormatStarts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Compilation
open Prob

section Marginals
variable {A B : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]

theorem pr_fst_coordinate (P : A → Prop) : pr (unif (A × B)) {u | P u.1} = pr (unif A) {a | P a} := by
  have hB0 : (Fintype.card B : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hBt : (Fintype.card B : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [pr_unif_eq (fun u : A × B => P u.1), pr_unif_eq P, cnt_fst P, Fintype.card_prod]
  push_cast
  exact ENNReal.mul_div_mul_right _ _ hB0 hBt

theorem pr_snd_coordinate (P : B → Prop) : pr (unif (A × B)) {u | P u.2} = pr (unif B) {b | P b} := by
  have hA0 : (Fintype.card A : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hAt : (Fintype.card A : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [pr_unif_eq (fun u : A × B => P u.2), pr_unif_eq P, cnt_snd P, Fintype.card_prod]
  push_cast
  exact ENNReal.mul_div_mul_left _ _ hA0 hAt

end Marginals

/-- **The mass of a run value in a set**, at a coin of two purses' kinds and two run values: the sum of its coordinates'. -/
theorem pr_runValues_le {A₂ A₃ R₂ R₃ : Type} [Fintype A₂] [Nonempty A₂] [Fintype A₃] [Nonempty A₃]
    [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Nonempty R₃] (P₂ : R₂ → Prop) (P₃ : R₃ → Prop) :
    pr (unif ((A₂ × R₂) × (A₃ × R₃))) {κ | P₂ κ.1.2 ∨ P₃ κ.2.2} ≤ pr (unif R₂) {r | P₂ r} + pr (unif R₃) {r | P₃ r} := by
  have e₂ : pr (unif ((A₂ × R₂) × (A₃ × R₃))) {κ | P₂ κ.1.2} = pr (unif R₂) {r | P₂ r} :=
    (pr_fst_coordinate (A := A₂ × R₂) (B := A₃ × R₃) fun u => P₂ u.2).trans (pr_snd_coordinate P₂)
  have e₃ : pr (unif ((A₂ × R₂) × (A₃ × R₃))) {κ | P₃ κ.2.2} = pr (unif R₃) {r | P₃ r} :=
    (pr_snd_coordinate (A := A₂ × R₂) (B := A₃ × R₃) fun u => P₃ u.2).trans (pr_snd_coordinate P₃)
  rw [← e₂, ← e₃]
  exact MeasureTheory.measure_union_le _ _

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.pr_fst_coordinate
#print axioms VerifiableInference.Compilation.pr_snd_coordinate
#print axioms VerifiableInference.Compilation.pr_runValues_le
