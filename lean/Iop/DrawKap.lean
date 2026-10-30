-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/DrawKap.lean: how large the bias of n blocks is: (1 + 2^-sl)^n ≤ 1 + 2^-e, if n · 2^(e + 1) ≤
2^sl. (Words of this library: lean/GLOSSARY.md.)
The bounds of a scheme over challenge samplers contain the factors κ₀^(blocks of a round) and
κ₀^(blocks of a protocol), κ₀ = 1 + 2^-sl (Iop/DrawOf.lean: `kapSl`). This is the one inequality
that turns them into numerals.
Proof: with x = 2^-sl, (1 + x)^n (1 − n x) ≤ ((1 + x)(1 − x))^n ≤ 1 by Bernoulli's inequality, and
1 / (1 − n x) ≤ 1 + 2 n x for n x ≤ 1/2.

Notation: `sl : ℕ`: in `DrawOf bE sl C` (Iop/DrawOf.lean), the slack of positions; `kapSl sl : ℝ≥0∞`
(there): the bias of one block; `n`, `e : ℕ`: arguments of `kapSl_pow_le`; what is asked of them:
`h`; block: a hash block, `Dig lam` (Iop/Wire.lean): lam bits.
-/
import Iop.DrawOf
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

namespace Iop
open scoped ENNReal

theorem real_pow_le {x : ℝ} (hx0 : 0 ≤ x) (n : ℕ) (h : (n : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ n ≤ 1 + 2 * (n * x) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hx1 : x ≤ 1 / 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith
  have hb : 1 + (n : ℝ) * (-x) ≤ (1 + -x) ^ n := one_add_mul_le_pow (by linarith) n
  have hp : (1 + x) ^ n * (1 + -x) ^ n ≤ 1 := by
    rw [← mul_pow]
    refine pow_le_one₀ (by nlinarith) (by nlinarith)
  have hpos : 0 ≤ (1 + x) ^ n := by positivity
  have h1 : (1 + x) ^ n * (1 - n * x) ≤ 1 := by
    have : (1 + x) ^ n * (1 + (n : ℝ) * (-x)) ≤ (1 + x) ^ n * (1 + -x) ^ n :=
      mul_le_mul_of_nonneg_left hb hpos
    nlinarith
  have h2 : (1 : ℝ) ≤ (1 + 2 * (n * x)) * (1 - n * x) := by
    nlinarith [mul_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) hx0]
  have h3 : (0 : ℝ) < 1 - n * x := by linarith
  have h4 : (1 + x) ^ n * (1 - n * x) ≤ (1 + 2 * (n * x)) * (1 - n * x) := le_trans h1 h2
  exact le_of_mul_le_mul_right h4 h3

/-- The bias of n blocks. -/
theorem kapSl_pow_le {sl n e : ℕ} (h : n * 2 ^ (e + 1) ≤ 2 ^ sl) :
    kapSl sl ^ n ≤ 1 + (2 ^ e : ℝ≥0∞)⁻¹ := by
  have hx0 : (0 : ℝ) ≤ ((2 : ℝ) ^ sl)⁻¹ := by positivity
  have e1 : kapSl sl = ENNReal.ofReal (1 + ((2 : ℝ) ^ sl)⁻¹) := by
    unfold kapSl
    rw [ENNReal.ofReal_add zero_le_one hx0, ENNReal.ofReal_one,
      ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have e2 : (1 + (2 ^ e : ℝ≥0∞)⁻¹) = ENNReal.ofReal (1 + ((2 : ℝ) ^ e)⁻¹) := by
    rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  have h' : (n : ℝ) * (2 : ℝ) ^ (e + 1) ≤ (2 : ℝ) ^ sl := by exact_mod_cast h
  have hnx : 2 * ((n : ℝ) * ((2 : ℝ) ^ sl)⁻¹) ≤ ((2 : ℝ) ^ e)⁻¹ := by
    rw [← mul_assoc, mul_inv_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity)]
    calc 2 * (n : ℝ) * 2 ^ e = n * 2 ^ (e + 1) := by rw [pow_succ]; ring
      _ ≤ _ := h'
  have hhalf : (n : ℝ) * ((2 : ℝ) ^ sl)⁻¹ ≤ 1 / 2 := by
    have : ((2 : ℝ) ^ e)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
    linarith
  rw [e1, e2, ← ENNReal.ofReal_pow (by positivity)]
  exact ENNReal.ofReal_le_ofReal (le_trans (real_pow_le hx0 n hhalf) (by linarith))

end Iop
