-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Prob/PowHalf.lean: (1 − 1/n)^n ≤ 1/2 in ℝ≥0∞, and its powers.

It is for probabilities of the form "none of many independent tries passes" whose exponent is too
large to be evaluated.

  `one_sub_inv_pow_le`       (1 − n⁻¹)^n ≤ 2⁻¹ for every natural number n ≠ 0
  `one_sub_inv_pow_mul_le`   (1 − n⁻¹)^(n · k) ≤ (2^k)⁻¹ for n ≠ 0

Proof. With y = 1/n and a = 1 − y: a (1 + y) ≤ a + y = 1, so a^n (1 + y)^n ≤ 1; and (1 + y)^n ≥ 1 +
n y = 2 (Bernoulli).

Limits: the true limit is 1/e; the constant 1/2 is what the short proof gives.
-/
import Mathlib

open scoped ENNReal

namespace Prob

theorem one_sub_inv_pow_le {n : ℕ} (hn : n ≠ 0) : (1 - ((n : ℝ≥0∞))⁻¹) ^ n ≤ (2 : ℝ≥0∞)⁻¹ := by
  have hn0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hnt : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hy1 : ((n : ℝ≥0∞))⁻¹ ≤ 1 :=
    ENNReal.inv_le_one.2 (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn)
  generalize hy : ((n : ℝ≥0∞))⁻¹ = y at hy1
  have hny : (n : ℝ≥0∞) * y = 1 := by rw [← hy]; exact ENNReal.mul_inv_cancel hn0 hnt
  have ha : (1 - y) + y = 1 := tsub_add_cancel_of_le hy1
  have h1 : (1 - y) * (1 + y) ≤ 1 := by
    rw [mul_add, mul_one]
    calc (1 - y) + (1 - y) * y ≤ (1 - y) + 1 * y := by gcongr; exact tsub_le_self
      _ = 1 := by rw [one_mul, ha]
  have h2 : (1 - y) ^ n * (1 + y) ^ n ≤ 1 := by
    rw [← mul_pow]
    exact pow_le_one' h1 n
  have h3 : (2 : ℝ≥0∞) ≤ (1 + y) ^ n := by
    have := one_add_mul_le_pow_of_sq_nonneg (a := y) (zero_le _) (zero_le _) (zero_le _) n
    rwa [hny, one_add_one_eq_two] at this
  have h4 : (1 - y) ^ n * 2 ≤ 1 := le_trans (by gcongr) h2
  rw [ENNReal.le_inv_iff_mul_le]
  exact h4

theorem one_sub_inv_pow_mul_le {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    (1 - ((n : ℝ≥0∞))⁻¹) ^ (n * k) ≤ ((2 : ℝ≥0∞) ^ k)⁻¹ := by
  rw [pow_mul, ENNReal.inv_pow]
  exact pow_le_pow_left' (one_sub_inv_pow_le hn) k

end Prob
