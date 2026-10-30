-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Field/MulEq.lean: the product on machine words is the product of Fmt/FieldE.lean.

The proof has two parts. `mulHi_spec`: the word from four products of halves is the product of the
two numbers divided by 2^64, rounded down. `toNat_reduceWide`: the reduction of a number of 128 bits
gives its residue modulo p.

Main theorems: `toNat_mulF`, `mulF_eq`. They hold for all words, also for words that are not
below p. Nothing is claimed here on whether these are the operations of a field. The long numerals
are 2^32, 2^64, p = 2^64 - 2^32 + 1 and 18446744065119617025 = (2^32 - 1)^2.
-/
import Mathlib.Tactic.Ring
import OnBytes.Field.WordEq

namespace OnBytes

/-- As a number, the low half of a word a is a modulo 2^32. -/
theorem toNat_lowHalf (a : UInt64) : (a &&& epsW).toNat = a.toNat % 4294967296 := by
  rw [UInt64.toNat_and, toNat_epsW]
  exact Nat.and_two_pow_sub_one_eq_mod a.toNat 32

/-- As a number, the high half of a word a is a / 2^32, rounded down. -/
theorem toNat_highHalf (a : UInt64) : (a >>> 32).toNat = a.toNat / 4294967296 := by
  rw [UInt64.toNat_shiftRight]
  exact Nat.shiftRight_eq_div_pow a.toNat 32

/-- As a number, a word a moved up by 32 bits is a 2^32 modulo 2^64. -/
theorem toNat_shiftUp (a : UInt64) :
    (a <<< 32).toNat = a.toNat * 4294967296 % 18446744073709551616 := by
  have h : (32 : UInt64).toNat % 64 = 32 := by decide
  have h32 : (2 : Nat) ^ 32 = 4294967296 := by decide
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := by decide
  rw [UInt64.toNat_shiftLeft, h, Nat.shiftLeft_eq, h32, h64]

/-- The product of two numbers, each given in halves, as a sum of the four products of halves. -/
theorem mul_halves (a0 a1 b0 b1 : Nat) : (a1 * 4294967296 + a0) * (b1 * 4294967296 + b0) =
    a1 * b1 * 18446744073709551616 + (a0 * b1 + a1 * b0) * 4294967296 + a0 * b0 := by
  ring

/-- A product of two numbers below 2^32 is at most (2^32 - 1)^2. -/
theorem half_mul_le {x y : Nat} (hx : x < 4294967296) (hy : y < 4294967296) :
    x * y ≤ 18446744065119617025 :=
  Nat.mul_le_mul (Nat.le_of_lt_succ hx) (Nat.le_of_lt_succ hy)

/-- The carries of `mulHi`, on numbers. The four products of halves are p00, p01, p10 and p11. -/
theorem mulHi_carries (p00 p01 p10 p11 : Nat) (h00 : p00 ≤ 18446744065119617025)
    (h01 : p01 ≤ 18446744065119617025) (h10 : p10 ≤ 18446744065119617025)
    (h11 : p11 ≤ 18446744065119617025) :
    ((p11 % 18446744073709551616 +
        (p01 % 18446744073709551616 + p00 % 18446744073709551616 / 4294967296) %
          18446744073709551616 / 4294967296) % 18446744073709551616 +
      (p10 % 18446744073709551616 +
        (p01 % 18446744073709551616 + p00 % 18446744073709551616 / 4294967296) %
          18446744073709551616 % 4294967296) % 18446744073709551616 / 4294967296) %
      18446744073709551616 =
    (p11 * 18446744073709551616 + (p01 + p10) * 4294967296 + p00) / 18446744073709551616 := by
  omega

/-- As a number, `mulHi a b` is a b / 2^64, rounded down. -/
theorem mulHi_spec (a b : UInt64) :
    (mulHi a b).toNat = a.toNat * b.toNat / 18446744073709551616 := by
  have ea : a.toNat = a.toNat / 4294967296 * 4294967296 + a.toNat % 4294967296 := by omega
  have eb : b.toNat = b.toNat / 4294967296 * 4294967296 + b.toNat % 4294967296 := by omega
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have la : a.toNat % 4294967296 < 4294967296 := by omega
  have lb : b.toNat % 4294967296 < 4294967296 := by omega
  have ua : a.toNat / 4294967296 < 4294967296 := by omega
  have ub : b.toNat / 4294967296 < 4294967296 := by omega
  have e : a.toNat * b.toNat =
      a.toNat / 4294967296 * (b.toNat / 4294967296) * 18446744073709551616 +
      (a.toNat % 4294967296 * (b.toNat / 4294967296) +
        a.toNat / 4294967296 * (b.toNat % 4294967296)) * 4294967296 +
      a.toNat % 4294967296 * (b.toNat % 4294967296) := by
    rw [← mul_halves, ← ea, ← eb]
  rw [e]
  unfold mulHi
  simp only [UInt64.toNat_add, UInt64.toNat_mul, toNat_lowHalf, toNat_highHalf]
  exact mulHi_carries _ _ _ _ (half_mul_le la lb) (half_mul_le la ub) (half_mul_le ua lb)
    (half_mul_le ua ub)

/-- `subMend a b` is congruent to a - b modulo p, for b below 2^32. -/
theorem subMend_spec (a b : UInt64) (hb : b.toNat < 4294967296) :
    ((subMend a b).toNat + b.toNat) % 18446744069414584321 = a.toNat % 18446744069414584321 := by
  have ha := a.toNat_lt
  unfold subMend
  by_cases h : a < b
  · rw [if_pos h, UInt64.toNat_sub, UInt64.toNat_sub, toNat_epsW]
    rw [UInt64.lt_iff_toNat_lt] at h
    omega
  · rw [if_neg h, UInt64.toNat_sub]
    rw [UInt64.lt_iff_toNat_lt] at h
    omega

/-- `addMend a b` is congruent to a + b modulo p, for b at most (2^32 - 1)^2. -/
theorem addMend_spec (a b : UInt64) (hb : b.toNat ≤ 18446744065119617025) :
    (addMend a b).toNat % 18446744069414584321 = (a.toNat + b.toNat) % 18446744069414584321 := by
  have ha := a.toNat_lt
  unfold addMend
  by_cases h : a + b < b
  · rw [if_pos h, UInt64.toNat_add, UInt64.toNat_add, toNat_epsW]
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
    omega
  · rw [if_neg h, UInt64.toNat_add]
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add] at h
    omega

/-- Modulo p: if t = lo - hi / 2^32 and r = t + (2^32 - 1) (hi % 2^32), then r = hi 2^64 + lo. -/
theorem reduceWide_nat (hi lo t r : Nat)
    (ht : (t + hi / 4294967296) % 18446744069414584321 = lo % 18446744069414584321)
    (hr : r % 18446744069414584321 =
      (t + (hi % 4294967296 * 4294967296 - hi % 4294967296)) % 18446744069414584321) :
    r % 18446744069414584321 = (hi * 18446744073709551616 + lo) % 18446744069414584321 := by
  omega

/-- As a number, `reduceWide hi lo` is hi 2^64 + lo modulo p. -/
theorem toNat_reduceWide (hi lo : UInt64) : (reduceWide hi lo).toNat =
    (hi.toNat * 18446744073709551616 + lo.toNat) % 18446744069414584321 := by
  have h1 := hi.toNat_lt
  have hh : (hi >>> 32).toNat < 4294967296 := by rw [toNat_highHalf]; omega
  have em : (((hi &&& epsW) <<< 32) - (hi &&& epsW)).toNat =
      hi.toNat % 4294967296 * 4294967296 - hi.toNat % 4294967296 := by
    rw [UInt64.toNat_sub, toNat_shiftUp, toNat_lowHalf]
    omega
  have hm : (((hi &&& epsW) <<< 32) - (hi &&& epsW)).toNat ≤ 18446744065119617025 := by
    rw [em]
    omega
  have ht := subMend_spec lo (hi >>> 32) hh
  have hr := addMend_spec (subMend lo (hi >>> 32)) _ hm
  rw [toNat_highHalf] at ht
  rw [em] at hr
  unfold reduceWide
  rw [toNat_normF]
  exact reduceWide_nat _ _ _ _ ht hr

/-- As a number, `mulF a b` is a b modulo p. -/
theorem toNat_mulF (a b : UInt64) :
    (mulF a b).toNat = a.toNat * b.toNat % 18446744069414584321 := by
  unfold mulF
  rw [toNat_reduceWide, mulHi_spec, UInt64.toNat_mul]
  congr 1
  omega

/-- The product on words is the product of Fmt/FieldE.lean. -/
theorem mulF_eq (a b : UInt64) : mulF a b = Fmt.Fld.two.mul a b := eq_red (toNat_mulF a b)

end OnBytes

#print axioms OnBytes.mulF_eq
