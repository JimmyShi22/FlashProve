-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Prob/TailSharp.lean: tools for sharp bounds on binomial tails, in natural numbers.

Prob/Tail.lean bounds the probability that one of M leaves is drawn more than s times in n uniform
draws by pOver M s n = M · Pr[Bin(n, 1/M) > s]. Its closed-form bounds are far from sharp near the
number of draws at which pOver crosses a given level.

The method. Two neighbouring terms `tailTerm M n j` = C(n, j) (M - 1)^(n - j) of the tail have the
exact ratio
      tailTerm M n (j + 1) · (j + 1) (M - 1) = tailTerm M n j · (n - j)   (`tailTerm_succ_mul`).
The tail from the term j on, `tailCount M n j` (Prob/Tail.lean), is
  * at least its first term (`tailTerm_le_tailCount`),
  * if D > N, at most its first term times D / (D - N), a geometric series, with D = (j + 1)(M - 1),
    N = n - j (`tailCount_mul_sub_le`).
For M > 0, pOver M s n ≤ 2^(-e) and 2^(-e) ≤ pOver M s n are equivalent to inequalities between
natural numbers (`pOver_le_inv_two_pow_iff`, `inv_two_pow_le_pOver_iff`).
Since pOver grows with n, two such facts at n₀ and n₀ + 1 fix the range of n in which pOver is at
most a level (`pOver_le_iff_of_cross`).

Limits: this file does not compute the first terms of a tail, and it has no numbers of draws at
which pOver crosses a level.
-/
import Prob.Tail
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic

set_option autoImplicit false

open scoped ENNReal Nat

namespace Prob

/-! ## 1. Neighbouring terms -/

/-- The exact ratio of two neighbouring terms. -/
theorem tailTerm_succ_mul (M n j : ℕ) :
    tailTerm M n (j + 1) * ((j + 1) * (M - 1)) = tailTerm M n j * (n - j) := by
  unfold tailTerm
  by_cases h : j < n
  · have h1 := Nat.choose_succ_right_eq n j
    have h2 : (M - 1) ^ (n - j) = (M - 1) ^ (n - (j + 1)) * (M - 1) := by
      rw [← pow_succ]
      congr 1
      omega
    calc n.choose (j + 1) * (M - 1) ^ (n - (j + 1)) * ((j + 1) * (M - 1))
        = (n.choose (j + 1) * (j + 1)) * ((M - 1) ^ (n - (j + 1)) * (M - 1)) := by ring
      _ = n.choose j * (n - j) * (M - 1) ^ (n - j) := by rw [h1, ← h2]
      _ = n.choose j * (M - 1) ^ (n - j) * (n - j) := by ring
  · have h0 : n - j = 0 := by omega
    rw [h0, Nat.choose_eq_zero_of_lt (by omega : n < j + 1)]
    simp

/-- The tail is its first term and the tail from the next term on. -/
theorem tailCount_eq_add (M n j : ℕ) :
    tailCount M n j = tailTerm M n j + tailCount M n (j + 1) := by
  by_cases h : j ≤ n
  · unfold tailCount
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega : j < n + 1)]
  · rw [tailCount_eq_zero (by omega), tailCount_eq_zero (by omega), tailTerm_eq_zero (by omega)]

theorem tailTerm_le_tailCount (M n j : ℕ) : tailTerm M n j ≤ tailCount M n j := by
  rw [tailCount_eq_add]
  exact Nat.le_add_right _ _

/-- The first term without a binomial coefficient. -/
theorem tailTerm_mul_factorial (M n r : ℕ) :
    tailTerm M n r * r ! = n.descFactorial r * (M - 1) ^ (n - r) := by
  unfold tailTerm
  rw [Nat.descFactorial_eq_factorial_mul_choose]
  ring

/-! ## 2. What is left: a geometric series -/

/-- If D > N, the tail is at most its first term times D / (D - N), with D = (r + 1)(M - 1) and
N = n - r. -/
theorem tailCount_mul_sub_le (M n r : ℕ) :
    tailCount M n r * ((r + 1) * (M - 1) - (n - r)) ≤ tailTerm M n r * ((r + 1) * (M - 1)) := by
  have hstep : ∀ j ∈ Finset.Ico r n,
      tailTerm M n (j + 1) * ((r + 1) * (M - 1)) ≤ tailTerm M n j * (n - r) := fun j hj => by
    have hrj : r ≤ j := (Finset.mem_Ico.1 hj).1
    calc tailTerm M n (j + 1) * ((r + 1) * (M - 1)) ≤ tailTerm M n (j + 1) * ((j + 1) * (M - 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
      _ = tailTerm M n j * (n - j) := tailTerm_succ_mul M n j
      _ ≤ tailTerm M n j * (n - r) := Nat.mul_le_mul_left _ (by omega)
  have hrest : tailCount M n (r + 1) * ((r + 1) * (M - 1)) ≤ tailCount M n r * (n - r) := by
    unfold tailCount
    rw [← Finset.sum_Ico_add' (fun j => tailTerm M n j) r n 1, Finset.sum_mul, Finset.sum_mul]
    refine (Finset.sum_le_sum hstep).trans ?_
    exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico le_rfl (Nat.le_succ n))
  rw [Nat.mul_sub, Nat.sub_le_iff_le_add]
  calc tailCount M n r * ((r + 1) * (M - 1))
      = tailTerm M n r * ((r + 1) * (M - 1)) + tailCount M n (r + 1) * ((r + 1) * (M - 1)) := by
        rw [tailCount_eq_add M n r]; ring
    _ ≤ tailTerm M n r * ((r + 1) * (M - 1)) + tailCount M n r * (n - r) :=
      Nat.add_le_add_left hrest _

/-! ## 3. pOver and inequalities between natural numbers -/

/-! ### From natural numbers to pOver -/

theorem pOver_le_inv_two_pow_iff {M : ℕ} (hM : 0 < M) (s n e : ℕ) :
    pOver M s n ≤ (2 ^ e : ℝ≥0∞)⁻¹ ↔ M * 2 ^ e * tailCount M n (s + 1) ≤ M ^ n := by
  have hY0 : ((M : ℝ≥0∞) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hM.ne')
  have hYt : ((M : ℝ≥0∞) ^ n) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  have h20 : ((2 : ℝ≥0∞) ^ e) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2t : ((2 : ℝ≥0∞) ^ e) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  unfold pOver binTail hitTail
  rw [← mul_div_assoc, ENNReal.div_le_iff hY0 hYt, ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (Or.inl h20) (Or.inl h2t)]
  constructor
  · intro h
    have h' : ((M * tailCount M n (s + 1) * 2 ^ e : ℕ) : ℝ≥0∞) ≤ ((M ^ n : ℕ) : ℝ≥0∞) := by
      push_cast; exact h
    have := Nat.cast_le.1 h'
    calc M * 2 ^ e * tailCount M n (s + 1) = M * tailCount M n (s + 1) * 2 ^ e := by ring
      _ ≤ M ^ n := this
  · intro h
    have h' : M * tailCount M n (s + 1) * 2 ^ e ≤ M ^ n := by
      calc M * tailCount M n (s + 1) * 2 ^ e = M * 2 ^ e * tailCount M n (s + 1) := by ring
        _ ≤ M ^ n := h
    exact_mod_cast h'

theorem inv_two_pow_le_pOver_iff {M : ℕ} (hM : 0 < M) (s n e : ℕ) :
    (2 ^ e : ℝ≥0∞)⁻¹ ≤ pOver M s n ↔ M ^ n ≤ M * 2 ^ e * tailCount M n (s + 1) := by
  have hY0 : ((M : ℝ≥0∞) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hM.ne')
  have hYt : ((M : ℝ≥0∞) ^ n) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
  have h20 : ((2 : ℝ≥0∞) ^ e) ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2t : ((2 : ℝ≥0∞) ^ e) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  unfold pOver binTail hitTail
  rw [← mul_div_assoc, ENNReal.le_div_iff_mul_le (Or.inl hY0) (Or.inl hYt),
    ← ENNReal.div_eq_inv_mul, ENNReal.div_le_iff h20 h2t]
  constructor
  · intro h
    have h' : ((M ^ n : ℕ) : ℝ≥0∞) ≤ ((M * tailCount M n (s + 1) * 2 ^ e : ℕ) : ℝ≥0∞) := by
      push_cast; exact h
    have := Nat.cast_le.1 h'
    calc M ^ n ≤ M * tailCount M n (s + 1) * 2 ^ e := this
      _ = M * 2 ^ e * tailCount M n (s + 1) := by ring
  · intro h
    have h' : M ^ n ≤ M * tailCount M n (s + 1) * 2 ^ e := by
      calc M ^ n ≤ M * 2 ^ e * tailCount M n (s + 1) := h
        _ = M * tailCount M n (s + 1) * 2 ^ e := by ring
    exact_mod_cast h'

/-- For M > 0, if a level is crossed between n₀ and n₀ + 1 draws (two facts in natural numbers),
pOver ≤ 2^(-e) if and only if n ≤ n₀. -/
theorem pOver_le_iff_of_cross {M : ℕ} (hM : 0 < M) (s e n₀ : ℕ)
    (hle : M * 2 ^ e * tailCount M n₀ (s + 1) ≤ M ^ n₀)
    (hlt : M ^ (n₀ + 1) < M * 2 ^ e * tailCount M (n₀ + 1) (s + 1)) (n : ℕ) :
    pOver M s n ≤ (2 ^ e : ℝ≥0∞)⁻¹ ↔ n ≤ n₀ := by
  constructor
  · intro h
    by_contra hn
    have h1 : pOver M s (n₀ + 1) ≤ (2 ^ e : ℝ≥0∞)⁻¹ :=
      (pOver_mono M s (by omega : n₀ + 1 ≤ n)).trans h
    exact absurd ((pOver_le_inv_two_pow_iff hM s (n₀ + 1) e).1 h1) (not_le.2 hlt)
  · intro h
    exact (pOver_mono M s h).trans ((pOver_le_inv_two_pow_iff hM s n₀ e).2 hle)

/-- `pOver_le_iff_of_cross` for "at least 2^(-e)". -/
theorem le_pOver_iff_of_cross {M : ℕ} (hM : 0 < M) (s e n₀ : ℕ)
    (hlt : M * 2 ^ e * tailCount M n₀ (s + 1) < M ^ n₀)
    (hle : M ^ (n₀ + 1) ≤ M * 2 ^ e * tailCount M (n₀ + 1) (s + 1)) (n : ℕ) :
    (2 ^ e : ℝ≥0∞)⁻¹ ≤ pOver M s n ↔ n₀ < n := by
  constructor
  · intro h
    by_contra hn
    have h1 : (2 ^ e : ℝ≥0∞)⁻¹ ≤ pOver M s n₀ := h.trans (pOver_mono M s (by omega : n ≤ n₀))
    exact absurd ((inv_two_pow_le_pOver_iff hM s n₀ e).1 h1) (not_le.2 hlt)
  · intro h
    exact ((inv_two_pow_le_pOver_iff hM s (n₀ + 1) e).2 hle).trans (pOver_mono M s h)

end Prob
