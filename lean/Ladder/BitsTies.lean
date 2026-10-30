-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ladder/BitsTies.lean: short theorems between the goals with a security level (Ladder/Bits.lean), and
from these to the goals of Ladder.lean.

Main statements.
  `g7bits_of_g8bits`, `g7bits_of_g7'bits`: between the goals with a level.
  `bits_le_ceiling`, `bitsBinding_le_ceiling`: up to the budgets of Ladder.lean (2^64 queries of the
    adversary, 2^64 of a parser) both errors are at most the ceiling of one quarter.
  `g7_of_g7bits`, `g7'_of_g7'bits`, `g8_of_g8bits`, `g9_of_g9bits`: each goal with a level gives the
    like-numbered goal of Ladder.lean.

-/
import Ladder.Bits
import Ladder.Ties

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifierAndGoals
open scoped ENNReal

/-- **G8bits gives G7bits.** -/
theorem g7bits_of_g8bits (D : SecondHashFunctionType → Description) (h : G8bits D) : G7bits D :=
  ⟨h.1, soundAt_of_soundUnderPolicyAt _ _ h.2⟩

/-- **G7'bits gives G7bits.** -/
theorem g7bits_of_g7'bits (D : SecondHashFunctionType → Description) (h : G7'bits D) : G7bits D := h _

/-- A natural number that is at most 2^k, over 2^(k + 3), is at most one eighth. -/
theorem div_le_eighth (a k : ℕ) (h : a ≤ 2 ^ k) : (a : ℝ≥0∞) / 2 ^ (k + 3) ≤ 8⁻¹ := by
  refine ENNReal.div_le_of_le_mul ?_
  have e : (8 : ℝ≥0∞)⁻¹ * 2 ^ (k + 3) = 2 ^ k := by
    rw [pow_add, mul_comm ((2 : ℝ≥0∞) ^ k), ← mul_assoc]
    norm_num
    rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  rw [e]
  exact_mod_cast h

theorem eighths : (8 : ℝ≥0∞)⁻¹ + 8⁻¹ = 4⁻¹ := by
  rw [← two_mul, show (8 : ℝ≥0∞) = 2 * 4 by norm_num,
    ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- **Up to the budgets the error "soundnessErrorInQueries" is at most the ceiling.** -/
theorem bits_le_ceiling (t n : ℕ) (ht : t ≤ queryBudget) (hn : n ≤ parserBudget) :
    soundnessErrorInQueries t n ≤ ceiling := by
  unfold queryBudget at ht
  unfold parserBudget at hn
  unfold soundnessErrorInQueries ceiling errorFactorPerQuery verifierQueryAllowance
  rw [← eighths, ← ENNReal.inv_pow, ← div_eq_mul_inv]
  refine add_le_add (div_le_eighth _ 125 ?_) (div_le_eighth _ 253 ?_)
  · norm_num at ht hn ⊢
    omega
  · calc (t + n + 2 ^ 23 + 2) ^ 2 ≤ (2 ^ 66) ^ 2 := Nat.pow_le_pow_left (by norm_num at ht hn ⊢; omega) 2
      _ ≤ 2 ^ 253 := by norm_num

/-- **Up to the budget the error "bindingErrorInQueries" is at most the ceiling.** -/
theorem bitsBinding_le_ceiling (t : ℕ) (ht : t ≤ queryBudget) : bindingErrorInQueries t ≤ ceiling := by
  unfold queryBudget at ht
  unfold bindingErrorInQueries ceiling errorFactorPerQuery verifierQueryAllowance honestBudget
  rw [← eighths, ← ENNReal.inv_pow, ← div_eq_mul_inv]
  refine add_le_add (div_le_eighth _ 125 ?_) (div_le_eighth _ 253 ?_)
  · norm_num at ht ⊢
    omega
  · calc (t + 2 ^ 48 + 2 ^ 23 + 2) ^ 2 ≤ (2 ^ 66) ^ 2 := Nat.pow_le_pow_left (by norm_num at ht ⊢; omega) 2
      _ ≤ 2 ^ 253 := by norm_num

/-- **G7bits gives G7.** -/
theorem g7_of_g7bits (D : SecondHashFunctionType → Description) (h : G7bits D) : G7 D :=
  ⟨soundnessErrorInQueries, bits_le_ceiling, h.2⟩

/-- **G7'bits gives G7'.** -/
theorem g7'_of_g7'bits (D : SecondHashFunctionType → Description) (h : G7'bits D) : G7' D :=
  ⟨soundnessErrorInQueries, bits_le_ceiling, fun o => (h o).2⟩

/-- **G8bits gives G8.** -/
theorem g8_of_g8bits (D : SecondHashFunctionType → Description) (h : G8bits D) : G8 D :=
  ⟨soundnessErrorInQueries, bits_le_ceiling, h.2⟩

/-- **G9bits gives G9.** -/
theorem g9_of_g9bits (D : SecondHashFunctionType → Description) (h : G9bits D) : G9 D :=
  ⟨bindingErrorInQueries, bitsBinding_le_ceiling, h⟩

end VerifierAndGoals

#print axioms VerifierAndGoals.g7bits_of_g8bits
#print axioms VerifierAndGoals.g7bits_of_g7'bits
#print axioms VerifierAndGoals.bits_le_ceiling
#print axioms VerifierAndGoals.bitsBinding_le_ceiling
#print axioms VerifierAndGoals.g7_of_g7bits
#print axioms VerifierAndGoals.g7'_of_g7'bits
#print axioms VerifierAndGoals.g8_of_g8bits
#print axioms VerifierAndGoals.g9_of_g9bits
