-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/CompletenessAndZeroKnowledge/StopsNumberAt154.lean: the inequality on the three numbers of private stops, at the numbers at which the
theorem on zero knowledge of the interactive protocol ends: 0, 0 and 2^-174; within the least power of one half that the
sum fits.

  window_is_a_power    ENNReal.ofReal (2 ^ (-174)) is (2⁻¹) ^ 174
  stops_sum            2^-157 + (0 + 0 + 688127 · 2^-174) = (2^17 + 688127) · 2^-174, that is 819199 · 2^-174
  stops_number_154     the sum is at most 2^-154
  stops_number_not_155 control: the sum is not at most 2^-155

Limits. Arithmetic alone. That any prover has these numbers is no part of this file. 2^-154 is a number that the sum fits,
not a target that anybody has named.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open scoped ENNReal

namespace VerifiableInference.Compilation

theorem window_is_a_power : ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ)) = ((2 : ℝ≥0∞)⁻¹) ^ 174 := by
  have e : (2 : ℝ) ^ (-174 : ℝ) = ((2 : ℝ)⁻¹) ^ (174 : ℕ) := by
    rw [Real.rpow_neg (by norm_num), inv_pow]
    norm_num
  rw [e, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

local notation "u" => (2⁻¹ : ℝ≥0∞)

/-- The sum as a multiple of 2^-174. -/
theorem stops_sum :
    u ^ 157 + ((0 : ℝ≥0∞) + 0 + (688127 : ℕ) * ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) =
      ((2 : ℝ≥0∞) ^ 17 + ((688127 : ℕ) : ℝ≥0∞)) * u ^ 174 := by
  have up : (2 : ℝ≥0∞) ^ 17 * u ^ (17 + 157) = u ^ 157 := by
    rw [pow_add, ← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow,
      one_mul]
  have h17 : u ^ 157 = (2 : ℝ≥0∞) ^ 17 * u ^ 174 := up.symm
  rw [window_is_a_power, add_zero, zero_add, add_mul, ← h17]

/-- **The inequality at 0, 0 and 2^-174, within 2^-154.** -/
theorem stops_number_154 :
    u ^ 157 + ((0 : ℝ≥0∞) + 0 + (688127 : ℕ) * ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) ≤ u ^ 154 := by
  have hle : (2 : ℝ≥0∞) ^ 17 + ((688127 : ℕ) : ℝ≥0∞) ≤ 2 ^ 20 := by
    exact_mod_cast (by norm_num : (2 : ℕ) ^ 17 + 688127 ≤ 2 ^ 20)
  have up : (2 : ℝ≥0∞) ^ 20 * u ^ (20 + 154) = u ^ 154 := by
    rw [pow_add, ← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow,
      one_mul]
  have h20 : (2 : ℝ≥0∞) ^ 20 * u ^ 174 = u ^ 154 := up
  rw [stops_sum, ← h20]
  exact mul_le_mul' hle le_rfl

/-- Control: the sum is above 2^-155. -/
theorem stops_number_not_155 :
    ¬ (u ^ 157 + ((0 : ℝ≥0∞) + 0 + (688127 : ℕ) * ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) ≤ u ^ 155) := by
  intro h
  have up : (2 : ℝ≥0∞) ^ 19 * u ^ (19 + 155) = u ^ 155 := by
    rw [pow_add, ← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow,
      one_mul]
  have h19 : (2 : ℝ≥0∞) ^ 19 * u ^ 174 = u ^ 155 := up
  have one : (2 : ℝ≥0∞) ^ 174 * u ^ 174 = 1 := by
    rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
  rw [stops_sum, ← h19] at h
  have k := mul_le_mul' (le_refl ((2 : ℝ≥0∞) ^ 174)) h
  rw [mul_left_comm ((2 : ℝ≥0∞) ^ 174) ((2 : ℝ≥0∞) ^ 17 + ((688127 : ℕ) : ℝ≥0∞)) (u ^ 174),
    mul_left_comm ((2 : ℝ≥0∞) ^ 174) ((2 : ℝ≥0∞) ^ 19) (u ^ 174), one, mul_one, mul_one] at k
  have kn : (2 : ℕ) ^ 17 + 688127 ≤ 2 ^ 19 := by exact_mod_cast k
  exact absurd kn (by norm_num)

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.window_is_a_power
#print axioms VerifiableInference.Compilation.stops_sum
#print axioms VerifiableInference.Compilation.stops_number_154
#print axioms VerifiableInference.Compilation.stops_number_not_155
