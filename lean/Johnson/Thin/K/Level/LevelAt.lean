-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Thin/K/Level/LevelAt.lean: the arithmetic behind the soundness bound, on bare numbers, at a
bound 2^-a on a round's error that need not be 2^-128.

Statements and proofs, one definition. The bounds of the library's compilers have the form
n · e + 2 (n + 1)² / 2^256: n a number of queries (the adversary's, the verifier's own, and whatever
factor a proof puts on their sum), e a bound on every round's error.

Main names:
  `level_at`: if a + s = 128, e ≤ c · 2^-a, c ≤ 1 + 1/4, n + 1 ≤ 2^j and j + s ≤ 126, then
    n · e + 2 (n + 1)² / 2^256 ≤ 2^-(127 - (j + s)), which is 2^-(a - 1 - j). By `level_arith`
    and `Val2.level_pow` (Johnson/Thin/K/Level/Arith.lean) at (n + 1) · 2^s.
  `level_at_lin`: under the same premises but with (n + 1) · 2^s ≤ 2^126 for the last two:
    n · e + 2 (n + 1)² / 2^256 ≤ (n + 1) · 2^s · 2^-127, which is (n + 1) · 2^-(a - 1): linear in n.
  `levelAt s N`: the closed step function: 2^-(127 - (j + s)) at j the least number with
    N ≤ 2^j, if j + s ≤ 126; else ⊤.
  `level_at_le`: under the first three premises,
    n · e + 2 (n + 1)² / 2^256 ≤ levelAt s (n + 1).
  `levelAt_mono`: it grows with N.
  `levelAt_le`: N ≤ 2^j and j + s ≤ 126 give levelAt s N ≤ 2^-(127 - (j + s)).

Limits: arithmetic on a formula. The hash length 256 is fixed in it, and a ≤ 128. It does not say
that the formula bounds anything, nor that any data meet the premises. Against the formula the step
function gives away up to a factor 2 for the power of two above N, and the factor 8/5 that
`level_arith` gives away.


-/
import Johnson.Thin.K.Level.Arith

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace TopC
open scoped ENNReal

/-- The arithmetic, linear in the number of queries: n queries, e a bound on every round's error,
2^-a with a + s = 128. -/
theorem level_at_lin (a s n : ℕ) (e c : ℝ≥0∞) (has : a + s = 128)
    (he : e ≤ c * ((2 : ℝ≥0∞) ^ a)⁻¹) (hc : c ≤ 1 + (4 : ℝ≥0∞)⁻¹)
    (hn : (n + 1) * 2 ^ s ≤ 2 ^ 126) :
    (n : ℝ≥0∞) * e + 2 * ((n + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 ≤
      (((n + 1) * 2 ^ s : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 127)⁻¹ := by
  have hsplit : ((2 : ℝ≥0∞) ^ a)⁻¹ = 2 ^ s * ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
    have h := inv_pow_split a s
    rwa [has] at h
  have h1 : (n : ℝ≥0∞) * e ≤
      (((n + 1) * 2 ^ s : ℕ) : ℝ≥0∞) * (c * ((2 : ℝ≥0∞) ^ 128)⁻¹) := by
    calc
      (n : ℝ≥0∞) * e ≤ ((n + 1 : ℕ) : ℝ≥0∞) * (c * (2 ^ s * ((2 : ℝ≥0∞) ^ 128)⁻¹)) :=
        mul_le_mul' (by exact_mod_cast Nat.le_succ n) (hsplit ▸ he)
      _ = (((n + 1) * 2 ^ s : ℕ) : ℝ≥0∞) * (c * ((2 : ℝ≥0∞) ^ 128)⁻¹) := by
        push_cast
        ring
  have h2 : 2 * ((n + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 ≤
      2 * (((n + 1) * 2 ^ s : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := by
    have h3 : ((n + 1 : ℕ) : ℝ≥0∞) ≤ (((n + 1) * 2 ^ s : ℕ) : ℝ≥0∞) := by
      exact_mod_cast Nat.le_mul_of_pos_right _ (by positivity)
    gcongr
  exact le_trans (add_le_add h1 h2) (level_arith _ hn c hc)

/-- The same in levels. -/
theorem level_at (a s n j : ℕ) (e c : ℝ≥0∞) (has : a + s = 128)
    (he : e ≤ c * ((2 : ℝ≥0∞) ^ a)⁻¹) (hc : c ≤ 1 + (4 : ℝ≥0∞)⁻¹) (hn : n + 1 ≤ 2 ^ j)
    (hj : j + s ≤ 126) :
    (n : ℝ≥0∞) * e + 2 * ((n + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 ≤
      ((2 : ℝ≥0∞) ^ (127 - (j + s)))⁻¹ := by
  have hT : (n + 1) * 2 ^ s ≤ 2 ^ (j + s) := by
    rw [pow_add]
    exact Nat.mul_le_mul_right _ hn
  exact le_trans
    (level_at_lin a s n e c has he hc (le_trans hT (Nat.pow_le_pow_right (by norm_num) hj)))
    (Val2.level_pow _ (j + s) (by omega) hT)

/-- The closed step function. -/
def levelAt (s N : ℕ) : ℝ≥0∞ :=
  if Nat.clog 2 N + s ≤ 126 then ((2 : ℝ≥0∞) ^ (127 - (Nat.clog 2 N + s)))⁻¹ else ⊤

theorem level_at_le (a s n : ℕ) (e c : ℝ≥0∞) (has : a + s = 128)
    (he : e ≤ c * ((2 : ℝ≥0∞) ^ a)⁻¹) (hc : c ≤ 1 + (4 : ℝ≥0∞)⁻¹) :
    (n : ℝ≥0∞) * e + 2 * ((n + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 ≤ levelAt s (n + 1) := by
  unfold levelAt
  split
  · rename_i hj
    exact level_at a s n _ e c has he hc (Nat.le_pow_clog (by norm_num) _) hj
  · exact le_top

theorem levelAt_le (s N j : ℕ) (hN : N ≤ 2 ^ j) (hj : j + s ≤ 126) :
    levelAt s N ≤ ((2 : ℝ≥0∞) ^ (127 - (j + s)))⁻¹ := by
  have hc : Nat.clog 2 N ≤ j := Nat.clog_le_of_le_pow hN
  unfold levelAt
  rw [if_pos (by omega)]
  exact ENNReal.inv_le_inv.2 (pow_le_pow_right₀ (by norm_num) (by omega))

theorem levelAt_mono (s : ℕ) {N N' : ℕ} (h : N ≤ N') : levelAt s N ≤ levelAt s N' := by
  by_cases hj : Nat.clog 2 N' + s ≤ 126
  · refine le_trans (levelAt_le s N _ (le_trans h (Nat.le_pow_clog (by norm_num) _)) hj) ?_
    unfold levelAt
    rw [if_pos hj]
  · unfold levelAt
    rw [if_neg hj]
    exact le_top

end TopC

#print axioms TopC.level_at_lin
#print axioms TopC.level_at
#print axioms TopC.level_at_le
#print axioms TopC.levelAt_le
#print axioms TopC.levelAt_mono
