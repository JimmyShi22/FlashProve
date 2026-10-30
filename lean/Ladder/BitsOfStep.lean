-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Ladder/BitsOfStep.lean: FROM A ROUND's ERROR TO THE LEVEL OF THE WHOLE. Arithmetic alone.

`frame_le_bits`: let a round's error be at most 2 / 2^128 and the verifier's own count v of queries
at most 2^23 - 9. Then the compiler's bound, A εs + 2 (A + 1)² / 2^256 at A = 5 (t + 8 + n + v + 1),
with the commitment's (t + 8 + n + 2)² / 2^256, is at most `soundnessErrorInQueries t n` WHEREVER `soundnessErrorInQueries t n` IS BELOW
1. Beyond that it is not: the compiler's square term has the coefficient 50 where `soundnessErrorInQueries` has 1;
there an error of 1 or more says nothing, and nothing is lost.

-/
import Ladder.Bits

set_option autoImplicit false

namespace VerifierAndGoals
open scoped ENNReal

/-- The arithmetic in the natural numbers. P stands for 2^128. -/
theorem frame_le_bits_nat (P T A c : ℕ) (hT : 16 * T < P) (h1 : 1 ≤ T) (hA : A ≤ 5 * T)
    (hc : c ≤ T + 2) :
    A * 2 * P + 2 * (A + 1) ^ 2 + c ^ 2 ≤ 16 * T * P + (T + 2) ^ 2 := by
  have e1 : A * 2 * P ≤ 10 * T * P := by nlinarith
  have e2 : (A + 1) ^ 2 ≤ (5 * T + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have e3 : c ^ 2 ≤ (T + 2) ^ 2 := Nat.pow_le_pow_left hc 2
  have e4 : 2 * (5 * T + 1) ^ 2 ≤ 6 * T * P := by nlinarith
  nlinarith

/-- 1 / 2^128 is 2^128 / 2^256. -/
theorem inv_pow128 : ((2 : ℝ≥0∞) ^ 128)⁻¹ = ((2 ^ 128 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  have h0 : ((2 : ℝ≥0∞) ^ 128) ≠ 0 := by positivity
  have ht : ((2 : ℝ≥0∞) ^ 128) ≠ ⊤ := by finiteness
  have e : ((2 : ℝ≥0∞) ^ 256) = 2 ^ 128 * 2 ^ 128 := by rw [← pow_add]
  rw [e, ENNReal.mul_inv (Or.inl h0) (Or.inl ht), Nat.cast_pow, Nat.cast_ofNat, ← mul_assoc,
    ENNReal.mul_inv_cancel h0 ht, one_mul]

/-- `soundnessErrorInQueries` as one natural number over 2^256. -/
theorem bits_eq (t n : ℕ) :
    soundnessErrorInQueries t n = ((16 * (t + n + 2 ^ 23) * 2 ^ 128 + (t + n + 2 ^ 23 + 2) ^ 2 : ℕ) : ℝ≥0∞) *
      ((2 : ℝ≥0∞) ^ 256)⁻¹ := by
  unfold soundnessErrorInQueries errorFactorPerQuery verifierQueryAllowance
  rw [← ENNReal.inv_pow, inv_pow128, div_eq_mul_inv, ← mul_assoc, ← add_mul, ← Nat.cast_mul,
    ← Nat.cast_add]

/-- Where `soundnessErrorInQueries` is below 1, sixteen times the number of queries is below 2^128. -/
theorem lt_of_bits_lt_one (t n : ℕ) (h : soundnessErrorInQueries t n < 1) : 16 * (t + n + 2 ^ 23) < 2 ^ 128 := by
  by_contra hc
  have hc' : 2 ^ 128 ≤ 16 * (t + n + 2 ^ 23) := Nat.le_of_not_lt hc
  have h0 : ((2 : ℝ≥0∞) ^ 256) ≠ 0 := by positivity
  have ht : ((2 : ℝ≥0∞) ^ 256) ≠ ⊤ := by finiteness
  have big : (2 ^ 256 : ℕ) ≤ 16 * (t + n + 2 ^ 23) * 2 ^ 128 + (t + n + 2 ^ 23 + 2) ^ 2 := by
    have : (2 ^ 256 : ℕ) = 2 ^ 128 * 2 ^ 128 := by rw [← pow_add]
    rw [this]
    exact le_trans (Nat.mul_le_mul_right _ hc') (Nat.le_add_right _ _)
  have : (1 : ℝ≥0∞) ≤ soundnessErrorInQueries t n := by
    rw [bits_eq, ← ENNReal.mul_inv_cancel h0 ht]
    refine mul_le_mul_left ?_ _
    exact_mod_cast big
  exact absurd h (not_lt.2 this)

/-- **From a round's error to the level of the whole.** See the head. -/
theorem frame_le_bits (v t n : ℕ) (εs : ℝ≥0∞) (hε : εs ≤ 2 * ((2 : ℝ≥0∞) ^ 128)⁻¹)
    (hv : v + 9 ≤ 2 ^ 23) (hb : soundnessErrorInQueries t n < 1) :
    (((t + (8 + n) + 0 + v + 1) * (1 + 4) : ℕ) : ℝ≥0∞) * εs +
        2 * (((t + (8 + n) + 0 + v + 1) * (1 + 4) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 +
      (((t + (8 + n) + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 ≤ soundnessErrorInQueries t n := by
  have hT := lt_of_bits_lt_one t n hb
  have key := frame_le_bits_nat (2 ^ 128) (t + n + 2 ^ 23) ((t + (8 + n) + 0 + v + 1) * (1 + 4))
    (t + (8 + n) + 2) hT (by omega) (by omega) (by omega)
  rw [bits_eq]
  refine le_trans ?_ (mul_le_mul_left (Nat.cast_le.2 key) _)
  refine le_trans (add_le_add (add_le_add (mul_le_mul_right hε _) le_rfl) le_rfl) ?_
  rw [inv_pow128, div_eq_mul_inv, div_eq_mul_inv]
  push_cast
  ring_nf
  exact le_rfl

end VerifierAndGoals

#print axioms VerifierAndGoals.frame_le_bits
