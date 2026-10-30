-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/Points.lean: the points of a code of the format are different, and none is 0.

A code of length 2^a in Fmt/M1Codes.lean evaluates polynomials at the points `point a x`,
x < 2^a. To get the point of x, start from 7 and multiply, for each i < a at which x has the bit 1,
by a root of unity of order 2^(i + 1) (for i from 32 on: by the constant below itself). Each of
these roots is a power of one constant, `w32`. This file reads the points as elements of the
base field `Cb.Gl.F` and proves what a Reed-Solomon code needs of them.

How. The constant has order exactly 2^32 (two powers, evaluated by Lean's kernel). The point of x
is 7 times the constant to the power `expFrom x a 0`, the sum of 2^(31 - i) over the set bits i < a
of x (a set bit from 32 on, which only a above 32 reads, counts 1). For a up to 32 that exponent is
below 2^32, and it determines the bits of x below a.

Main definitions. (`ptOf a x`, the point of the position x as an element of the base field, is
defined in OnBytes/Slice/LinkAt.lean.)
 `rootW`            the constant, as an element of the base field.
 `expFrom x n i`    the exponent that the n bits of x from bit i on contribute.
Main theorems.
 `rootW_order`      the constant has order 2^32.
 `toF_point`        the point of x is 7 times the constant to the power `expFrom x a 0`.
 `ptOf_inj`         for a up to 32, different positions have different points.
 `ptOf_ne_zero`     no point is 0, for every a.

Not claimed. That the points differ at lengths above 2^32. Nothing on the codes' distance. Nothing
on the other field of the format.
-/
import Fmt.M1Codes
import OnBytes.Slice.Field
import OnBytes.Slice.LinkAt

set_option autoImplicit false

namespace OnBytes.Slice
open Code

/-- The format's root of unity of order 2^32, as an element of the base field. -/
def rootW : Cb.Gl.F := toF Fmt.M1.w32

/-- The exponent that the n bits of x from bit i on contribute: bit j gives 2^(32 - (j + 1)) if it
is set. -/
def expFrom (x : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, i => (if x.testBit i = true then 2 ^ (32 - (i + 1)) else 0) + expFrom x n (i + 1)

/-! ## The constant has order 2^32 -/

/-- The constant, written as a number. -/
theorem rootW_eq : rootW = ((16334397945464290598 : ℕ) : Cb.Gl.F) := by
  have h : Fmt.M1.w32.toNat = 16334397945464290598 := by decide +kernel
  unfold rootW toF
  rw [h]

/-- The power 2^32 of the constant is 1. -/
theorem rootW_pow_top : rootW ^ 2 ^ (31 + 1) = 1 := by
  have h := natCast_pow_eq (m := pGold) (digits := 33) (a := 16334397945464290598)
    (n := 2 ^ (31 + 1)) (v := 1) (by decide +kernel) (by decide +kernel)
  rw [Nat.cast_one] at h
  rw [rootW_eq]
  exact h

/-- The power 2^31 of the constant is not 1. -/
theorem rootW_pow_half : ¬ rootW ^ 2 ^ 31 = 1 := by
  rw [rootW_eq]
  exact natCast_pow_ne_one (m := pGold) (digits := 32) (a := 16334397945464290598) (n := 2 ^ 31)
    (v := 18446744069414584320) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The constant has order exactly 2^32. -/
theorem rootW_order : orderOf rootW = 2 ^ 32 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime_pow rootW_pow_half rootW_pow_top

/-- The constant is not 0. -/
theorem rootW_ne_zero : rootW ≠ 0 := by
  intro h
  have h1 := rootW_pow_top
  rw [h, zero_pow (pow_ne_zero _ (by norm_num))] at h1
  exact zero_ne_one h1

/-- The word 7 is not read as 0. -/
theorem toF_seven_ne_zero : toF 7 ≠ 0 := by
  show ((7 : ℕ) : Cb.Gl.F) ≠ 0
  exact natCast_ne_zero_of_lt FGold pGold (by norm_num) (by decide +kernel)

/-! ## A point is 7 times a power of the constant -/

/-- Squaring k times is the power 2^k. -/
theorem toF_sqN (x : UInt64) (k : ℕ) : toF (Fmt.M1.sqN x k) = toF x ^ 2 ^ k := by
  induction k generalizing x with
  | zero =>
    show toF x = toF x ^ 2 ^ 0
    rw [pow_zero, pow_one]
  | succ k ih =>
    show toF (Fmt.M1.sqN (Fmt.Fld.two.mul x x) k) = toF x ^ 2 ^ (k + 1)
    rw [ih, toF_mul, ← pow_two, ← pow_mul, ← pow_succ']

/-- The format's root of unity of order 2^j is a power of the constant. -/
theorem toF_rootOf2 (j : ℕ) : toF (Fmt.M1.rootOf2 j) = rootW ^ 2 ^ (32 - j) := by
  unfold Fmt.M1.rootOf2 rootW
  exact toF_sqN _ _

/-- The loop that multiplies the roots of the set bits multiplies by a power of the constant. -/
theorem toF_pointFrom (x n i : ℕ) (acc : UInt64) :
    toF (Fmt.M1.pointFrom x n i acc) = toF acc * rootW ^ expFrom x n i := by
  induction n generalizing i acc with
  | zero =>
    show toF acc = toF acc * rootW ^ 0
    rw [pow_zero, mul_one]
  | succ n ih =>
    show toF (Fmt.M1.pointFrom x n (i + 1)
        (if x.testBit i = true then Fmt.Fld.two.mul acc (Fmt.M1.rootOf2 (i + 1)) else acc)) =
      toF acc * rootW ^
        ((if x.testBit i = true then 2 ^ (32 - (i + 1)) else 0) + expFrom x n (i + 1))
    rw [ih, pow_add, ← mul_assoc]
    by_cases h : x.testBit i = true
    · rw [if_pos h, if_pos h, toF_mul, toF_rootOf2]
    · rw [if_neg h, if_neg h, pow_zero, mul_one]

/-- The point of x is 7 times the constant to the power `expFrom x a 0`. -/
theorem toF_point (a x : ℕ) : toF (Fmt.M1.point a x) = toF 7 * rootW ^ expFrom x a 0 :=
  toF_pointFrom x a 0 7

/-- No point is 0. -/
theorem toF_point_ne_zero (a x : ℕ) : toF (Fmt.M1.point a x) ≠ 0 := by
  rw [toF_point]
  exact mul_ne_zero toF_seven_ne_zero (pow_ne_zero _ rootW_ne_zero)

/-! ## The exponent is small and determines the bits -/

/-- The bits from i on contribute less than 2^(32 - i). -/
theorem expFrom_lt (x n i : ℕ) (h : i + n ≤ 32) : expFrom x n i < 2 ^ (32 - i) := by
  induction n generalizing i with
  | zero => exact Nat.two_pow_pos _
  | succ n ih =>
    have h1 : expFrom x n (i + 1) < 2 ^ (32 - (i + 1)) := ih (i + 1) (by omega)
    have h2 : 2 ^ (32 - i) = 2 ^ (32 - (i + 1)) + 2 ^ (32 - (i + 1)) := by
      rw [← two_mul, ← pow_succ']
      congr 1
      omega
    have h3 : (if x.testBit i = true then 2 ^ (32 - (i + 1)) else 0) ≤ 2 ^ (32 - (i + 1)) := by
      by_cases hb : x.testBit i = true
      · rw [if_pos hb]
      · rw [if_neg hb]
        exact Nat.zero_le _
    show (if x.testBit i = true then 2 ^ (32 - (i + 1)) else 0) + expFrom x n (i + 1) <
      2 ^ (32 - i)
    rw [h2]
    exact Nat.add_lt_add_of_le_of_lt h3 h1

/-- Equal exponents: equal bits. The first bit's share is larger than all that the later bits can
contribute together, so it can be read off the sum; then the same for the rest. -/
theorem expFrom_bits (x y n i : ℕ) (h : i + n ≤ 32) (he : expFrom x n i = expFrom y n i) :
    ∀ j, i ≤ j → j < i + n → x.testBit j = y.testBit j := by
  induction n generalizing i with
  | zero =>
    intro j h1 h2
    omega
  | succ n ih =>
    have hx : expFrom x n (i + 1) < 2 ^ (32 - (i + 1)) := expFrom_lt x n (i + 1) (by omega)
    have hy : expFrom y n (i + 1) < 2 ^ (32 - (i + 1)) := expFrom_lt y n (i + 1) (by omega)
    have he' : (if x.testBit i = true then 2 ^ (32 - (i + 1)) else 0) + expFrom x n (i + 1) =
        (if y.testBit i = true then 2 ^ (32 - (i + 1)) else 0) + expFrom y n (i + 1) := he
    have key : x.testBit i = y.testBit i ∧ expFrom x n (i + 1) = expFrom y n (i + 1) := by
      by_cases bx : x.testBit i = true <;> by_cases bz : y.testBit i = true
      · rw [if_pos bx, if_pos bz] at he'
        exact ⟨bx.trans bz.symm, Nat.add_left_cancel he'⟩
      · rw [if_pos bx, if_neg bz] at he'
        exfalso
        omega
      · rw [if_neg bx, if_pos bz] at he'
        exfalso
        omega
      · rw [if_neg bx, if_neg bz] at he'
        exact ⟨(eq_false_of_ne_true bx).trans (eq_false_of_ne_true bz).symm,
          Nat.add_left_cancel he'⟩
    intro j h1 h2
    rcases Nat.eq_or_lt_of_le h1 with h3 | h3
    · rw [← h3]
      exact key.1
    · exact ih (i + 1) (by omega) key.2 j h3 (by omega)

/-! ## The points are different -/

/-- For a up to 32, positions below 2^a with the same point are the same. -/
theorem toF_point_inj (a : ℕ) (ha : a ≤ 32) {x y : ℕ} (hx : x < 2 ^ a) (hy : y < 2 ^ a)
    (h : toF (Fmt.M1.point a x) = toF (Fmt.M1.point a y)) : x = y := by
  rw [toF_point, toF_point] at h
  have h1 : rootW ^ expFrom x a 0 = rootW ^ expFrom y a 0 :=
    mul_left_cancel₀ toF_seven_ne_zero h
  have hxe : expFrom x a 0 ∈ Set.Iio (orderOf rootW) := by
    rw [rootW_order]
    exact Set.mem_Iio.2 (expFrom_lt x a 0 (by omega))
  have hye : expFrom y a 0 ∈ Set.Iio (orderOf rootW) := by
    rw [rootW_order]
    exact Set.mem_Iio.2 (expFrom_lt y a 0 (by omega))
  have h2 : expFrom x a 0 = expFrom y a 0 := pow_injOn_Iio_orderOf hxe hye h1
  have h3 : ∀ j, 0 ≤ j → j < 0 + a → x.testBit j = y.testBit j :=
    expFrom_bits x y a 0 (by omega) h2
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < a
  · exact h3 j (Nat.zero_le j) (by omega)
  · have hp : 2 ^ a ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (Nat.le_of_not_lt hj)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx hp),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy hp)]

/-- For a up to 32, different positions of a code of length 2^a have different points. -/
theorem ptOf_inj (a : ℕ) (ha : a ≤ 32) : Function.Injective (ptOf a) :=
  fun x y h => Fin.ext (toF_point_inj a ha x.isLt y.isLt h)

/-- No point is 0. -/
theorem ptOf_ne_zero (a : ℕ) (x : Fin (2 ^ a)) : ptOf a x ≠ 0 :=
  toF_point_ne_zero a x.val

end OnBytes.Slice

#print axioms OnBytes.Slice.rootW_order
#print axioms OnBytes.Slice.toF_point
#print axioms OnBytes.Slice.ptOf_inj
#print axioms OnBytes.Slice.ptOf_ne_zero
