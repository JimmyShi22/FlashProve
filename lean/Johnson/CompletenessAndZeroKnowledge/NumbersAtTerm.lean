-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CompletenessAndZeroKnowledge/NumbersAtTerm.lean: the inequality on the completeness error.

1.  WHAT IS CLAIMED: the searches' 71 · 2^-92, the half of 2^-40 left to completeness as an interactive oracle proof, and six times 2^-256 for the parser stay below 2^-40.
-/
import Mathlib

set_option autoImplicit false

open scoped ENNReal

namespace VerifiableInference.Compilation

theorem numbers_hold :
    71 * ((2 : ℝ≥0∞) ^ 92)⁻¹ + ((2 : ℝ≥0∞)⁻¹ ^ 40 / 2) +
        ((((2 : ℝ≥0∞) ^ 256)⁻¹ + (((2 : ℝ≥0∞) ^ 256)⁻¹ + ((2 : ℝ≥0∞) ^ 256)⁻¹)) +
          (((2 : ℝ≥0∞) ^ 256)⁻¹ + (((2 : ℝ≥0∞) ^ 256)⁻¹ + ((2 : ℝ≥0∞) ^ 256)⁻¹))) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 40 := by
  set u : ℝ≥0∞ := (2 : ℝ≥0∞)⁻¹ with hu
  have h1 : u ≤ 1 := ENNReal.inv_le_one.2 (by norm_num)
  have hp : ∀ n : ℕ, ((2 : ℝ≥0∞) ^ n)⁻¹ = u ^ n := fun n => ENNReal.inv_pow
  have hsum : u + u = 1 := ENNReal.inv_two_add_inv_two
  have hhalf : u ^ 40 / 2 = u ^ 41 := by
    rw [div_eq_mul_inv, ← hu]
    ring
  have h128 : (128 : ℝ≥0∞) * u ^ 7 = 1 := by
    have e : (128 : ℝ≥0∞) = 2 ^ 7 := by norm_num
    rw [e, ← mul_pow, hu, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  have h92 : (128 : ℝ≥0∞) * u ^ 92 ≤ u ^ 41 := by
    have e : u ^ 92 = u ^ 7 * u ^ 85 := by rw [← pow_add]
    rw [e, ← mul_assoc, h128, one_mul]
    exact pow_le_pow_right_of_le_one' h1 (by norm_num)
  have h256 : u ^ 256 ≤ u ^ 92 := pow_le_pow_right_of_le_one' h1 (by norm_num)
  simp only [hp, hhalf]
  have hsmall : 71 * u ^ 92 + ((u ^ 256 + (u ^ 256 + u ^ 256)) + (u ^ 256 + (u ^ 256 + u ^ 256))) ≤ u ^ 41 := by
    calc 71 * u ^ 92 + ((u ^ 256 + (u ^ 256 + u ^ 256)) + (u ^ 256 + (u ^ 256 + u ^ 256)))
        ≤ 71 * u ^ 92 + ((u ^ 92 + (u ^ 92 + u ^ 92)) + (u ^ 92 + (u ^ 92 + u ^ 92))) := by gcongr
      _ = 77 * u ^ 92 := by ring
      _ ≤ 128 * u ^ 92 := by gcongr; norm_num
      _ ≤ u ^ 41 := h92
  have e40 : u ^ 40 = u ^ 41 + u ^ 41 := by
    have : u ^ 41 + u ^ 41 = u ^ 40 * (u + u) := by ring
    rw [this, hsum, mul_one]
  calc 71 * u ^ 92 + u ^ 41 + ((u ^ 256 + (u ^ 256 + u ^ 256)) + (u ^ 256 + (u ^ 256 + u ^ 256)))
      = (71 * u ^ 92 + ((u ^ 256 + (u ^ 256 + u ^ 256)) + (u ^ 256 + (u ^ 256 + u ^ 256)))) + u ^ 41 := by ring
    _ ≤ u ^ 41 + u ^ 41 := by gcongr
    _ = u ^ 40 := e40.symm

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.numbers_hold
