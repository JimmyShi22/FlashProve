-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Thin/K/Level/Arith.lean: arithmetic on powers of two in `ℝ≥0∞`, behind the soundness bound.

Statements and proofs. Nothing here depends on a protocol.

Main names:
  `inv_pow_split`: (2^n)⁻¹ = 2^m · (2^(n + m))⁻¹.
  `level_arith`: if T ≤ 2^126 and c ≤ 1 + 1/4, then
    T · (c · 2^-128) + 2 T² / 2^256 ≤ T · 2^-127.
  `Val2.level_pow`: if j ≤ 127 and T ≤ 2^j, then T · 2^-127 ≤ 2^-(127 - j).

Limits: arithmetic on a formula. The hash length 256 and the number 2^-128 are fixed in it. It does
not say that the formula bounds anything, nor that any data meet the premises.

-/
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace TopC
open scoped ENNReal

theorem inv_pow_split (n m : ℕ) : ((2 : ℝ≥0∞) ^ n)⁻¹ = 2 ^ m * ((2 : ℝ≥0∞) ^ (n + m))⁻¹ := by
  have h0 : (2 : ℝ≥0∞) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have ht : (2 : ℝ≥0∞) ^ m ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  rw [pow_add, ENNReal.mul_inv (Or.inr ht) (Or.inr h0), mul_comm ((2 : ℝ≥0∞) ^ n)⁻¹, ← mul_assoc,
    ENNReal.mul_inv_cancel h0 ht, one_mul]

/-- the arithmetic, in one number T -/
theorem level_arith (T : ℕ) (hT : T ≤ 2 ^ 126) (c : ℝ≥0∞) (hc : c ≤ 1 + (4 : ℝ≥0∞)⁻¹) :
    (T : ℝ≥0∞) * (c * ((2 : ℝ≥0∞) ^ 128)⁻¹) + 2 * (T : ℝ≥0∞) ^ 2 / 2 ^ 256 ≤
      (T : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 127)⁻¹ := by
  have e128 : ((2 : ℝ≥0∞) ^ 128)⁻¹ = 2 ^ 2 * ((2 : ℝ≥0∞) ^ 130)⁻¹ := inv_pow_split 128 2
  have e129 : ((2 : ℝ≥0∞) ^ 129)⁻¹ = 2 ^ 1 * ((2 : ℝ≥0∞) ^ 130)⁻¹ := inv_pow_split 129 1
  have e127 : ((2 : ℝ≥0∞) ^ 127)⁻¹ = 2 ^ 3 * ((2 : ℝ≥0∞) ^ 130)⁻¹ := inv_pow_split 127 3
  have e256 : ((2 : ℝ≥0∞) ^ 129)⁻¹ = 2 ^ 127 * ((2 : ℝ≥0∞) ^ 256)⁻¹ := inv_pow_split 129 127
  have h1 : c * ((2 : ℝ≥0∞) ^ 128)⁻¹ ≤ 5 * ((2 : ℝ≥0∞) ^ 130)⁻¹ := by
    calc
      c * ((2 : ℝ≥0∞) ^ 128)⁻¹ ≤ (1 + (4 : ℝ≥0∞)⁻¹) * (2 ^ 2 * ((2 : ℝ≥0∞) ^ 130)⁻¹) := by
        rw [← e128]; exact mul_le_mul' hc le_rfl
      _ = ((1 + (4 : ℝ≥0∞)⁻¹) * 4) * ((2 : ℝ≥0∞) ^ 130)⁻¹ := by rw [← mul_assoc]; norm_num
      _ = 5 * ((2 : ℝ≥0∞) ^ 130)⁻¹ := by
          rw [add_mul, one_mul, ENNReal.inv_mul_cancel (by norm_num) (by norm_num)]; norm_num
  have h2 : 2 * (T : ℝ≥0∞) ^ 2 / 2 ^ 256 ≤ (T : ℝ≥0∞) * (2 * ((2 : ℝ≥0∞) ^ 130)⁻¹) := by
    have hT' : (T : ℝ≥0∞) ≤ 2 ^ 126 := by exact_mod_cast hT
    calc
      2 * (T : ℝ≥0∞) ^ 2 / 2 ^ 256 = (T : ℝ≥0∞) * (2 * (T : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 256)⁻¹) := by
        rw [ENNReal.div_eq_inv_mul]; ring
      _ ≤ (T : ℝ≥0∞) * (2 * 2 ^ 126 * ((2 : ℝ≥0∞) ^ 256)⁻¹) :=
        mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' le_rfl hT') le_rfl)
      _ = (T : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 129)⁻¹ := by rw [e256]; ring
      _ = (T : ℝ≥0∞) * (2 * ((2 : ℝ≥0∞) ^ 130)⁻¹) := by rw [e129]; ring
  calc
    (T : ℝ≥0∞) * (c * ((2 : ℝ≥0∞) ^ 128)⁻¹) + 2 * (T : ℝ≥0∞) ^ 2 / 2 ^ 256 ≤
        (T : ℝ≥0∞) * (5 * ((2 : ℝ≥0∞) ^ 130)⁻¹) + (T : ℝ≥0∞) * (2 * ((2 : ℝ≥0∞) ^ 130)⁻¹) :=
      add_le_add (mul_le_mul' le_rfl h1) h2
    _ = (T : ℝ≥0∞) * (7 * ((2 : ℝ≥0∞) ^ 130)⁻¹) := by ring
    _ ≤ (T : ℝ≥0∞) * (8 * ((2 : ℝ≥0∞) ^ 130)⁻¹) :=
      mul_le_mul' le_rfl (mul_le_mul' (by norm_num) le_rfl)
    _ = (T : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 127)⁻¹ := by rw [e127]; norm_num

end TopC

namespace TopC.Val2
open scoped ENNReal

/-- T ≤ 2^j, j ≤ 127:   T · 2^-127 ≤ 2^-(127 - j) -/
theorem level_pow (T j : ℕ) (hj : j ≤ 127) (hT : T ≤ 2 ^ j) :
    (T : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 127)⁻¹ ≤ ((2 : ℝ≥0∞) ^ (127 - j))⁻¹ := by
  have e := inv_pow_split (127 - j) j
  rw [Nat.sub_add_cancel hj] at e
  rw [e]
  exact mul_le_mul' (by exact_mod_cast hT) le_rfl

end TopC.Val2
