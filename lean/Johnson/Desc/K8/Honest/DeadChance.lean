-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/DeadChance.lean: THE SMALLNESS TEST: THE COUNT OF
Johnson/Desc/K8/Honest/DeadColumn.lean AS A CHANCE: over a uniform typed matrix some column is all 0
with a chance of at most columns / 2 ^ tau. One statement and its proof. No block, no state, no
prover. A lemma; none of the library's goals.

  **`dead_chance`**   by `dead_few` and Prob.pr_unif_le_iff (Prob/Count.lean)
Limits: those of DeadColumn.lean: uniform TYPED matrices (`Dr s`): nothing on written verifier
messages. No number is evaluated.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.DeadColumn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model Cb.Pv.Tail OnBytes.Tie.Pv.Tail
open scoped ENNReal

/-- **Some column of a uniform typed matrix is all 0.** -/
theorem dead_chance (s : Size) :
    Prob.pr (Prob.unif (Dr s))
        {β | ∃ (μ : Fin s.NM) (c : Fin (s.k μ)), ∀ u, (β μ u c).val = 0} ≤
      (s.columns : ℝ≥0∞) / 2 ^ s.tau := by
  rw [Prob.pr_unif_le_iff]
  have h0 : (2 : ℝ≥0∞) ^ s.tau ≠ 0 := pow_ne_zero _ two_ne_zero
  have ht : (2 : ℝ≥0∞) ^ s.tau ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  have hk : (Prob.cnt (fun β : Dr s =>
      ∃ (μ : Fin s.NM) (c : Fin (s.k μ)), ∀ u, (β μ u c).val = 0) : ℝ≥0∞) * 2 ^ s.tau ≤
      (s.columns : ℝ≥0∞) * Fintype.card (Dr s) := by
    exact_mod_cast dead_few s
  calc (Prob.cnt (fun β : Dr s =>
        ∃ (μ : Fin s.NM) (c : Fin (s.k μ)), ∀ u, (β μ u c).val = 0) : ℝ≥0∞)
      = (Prob.cnt (fun β : Dr s =>
          ∃ (μ : Fin s.NM) (c : Fin (s.k μ)), ∀ u, (β μ u c).val = 0) : ℝ≥0∞) * 2 ^ s.tau /
          2 ^ s.tau := (ENNReal.mul_div_cancel_right h0 ht).symm
    _ ≤ (s.columns : ℝ≥0∞) * Fintype.card (Dr s) / 2 ^ s.tau := ENNReal.div_le_div_right hk _
    _ = (s.columns : ℝ≥0∞) / 2 ^ s.tau * Fintype.card (Dr s) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.dead_chance
