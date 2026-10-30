-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/RepPoints.lean: powers of the points of a code of the format, and positions with
their low and high bits exchanged.

A code of length 2^a in Fmt/M1Codes.lean evaluates polynomials at the points `point a x`, each 7
times a power of one root of unity of order 2^32 (OnBytes/Slice/Points.lean). This file leaves out
the factor 7 (`unitPt`). It shows that the power 2^k of the point of x in a domain of length
2^(b + k) is the point of x / 2^k in the domain of length 2^b: raising to that power reads the high
bits of a position. A code of length 2^b that is repeated along 2^(b + k) positions is read at x
modulo 2^b, the low bits (`posIn`, OnBytes/Slice/LinkAt.lean). `turn` exchanges the two parts of a
position, so that the power 2^k of the point at the turned position is the short code's point,
without the 7, at x modulo 2^b. OnBytes/Slice/NumbersHalf.lean uses this.

Main definitions: `unitPt`, `turn`.
Main theorems.
 `unitPt_pow`   for b + k up to 32: unitPt (b + k) x ^ 2^k = unitPt b (x / 2^k).
 `unitPt_inj`   for a up to 32, positions below 2^a with the same point are the same.
 `turn_div`, `turn_mod`, `turn_lt`, `turn_inj`   for a position below 2^(b + k): the turned
                position divided by 2^k is the position modulo 2^b; modulo 2^k it is the position
                divided by 2^b; it is below 2^(b + k); different positions stay different.

Through OnBytes/Slice/Points.lean this file rests on two powers of the constant that Lean's kernel
evaluates (`rootW_pow_top`, `rootW_pow_half`).

Not claimed. Nothing at lengths above 2^32. Nothing on codes, distances or agreement. Nothing on the
other field of the format.

-/
import OnBytes.Slice.Points

set_option autoImplicit false

namespace OnBytes.Slice

/-- The point of x in a code of length 2^a, without the factor 7. -/
def unitPt (a x : ℕ) : Cb.Gl.F := rootW ^ expFrom x a 0

/-- The point of x is 7 times `unitPt a x`. -/
theorem toF_point_unit (a x : ℕ) : toF (Fmt.M1.point a x) = toF 7 * unitPt a x := toF_point a x

/-- Twice what the n bits of x from i + 1 on contribute is what the n bits of x / 2 from i on
contribute, for i + 1 + n ≤ 32. -/
theorem two_mul_expFrom (x n i : ℕ) (h : i + 1 + n ≤ 32) :
    2 * expFrom x n (i + 1) = expFrom (x / 2) n i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    show 2 * ((if x.testBit (i + 1) = true then 2 ^ (32 - (i + 1 + 1)) else 0) +
        expFrom x n (i + 1 + 1)) =
      (if (x / 2).testBit i = true then 2 ^ (32 - (i + 1)) else 0) + expFrom (x / 2) n (i + 1)
    rw [Nat.mul_add, ih (i + 1) (by omega), ← Nat.testBit_succ]
    congr 1
    by_cases hx : x.testBit (i + 1) = true
    · rw [if_pos hx, if_pos hx, ← pow_succ']
      congr 1
      omega
    · rw [if_neg hx, if_neg hx]

/-- For a + 1 ≤ 32: squaring a point of the longer domain gives the point of half the position in
the domain of half the length. -/
theorem unitPt_sq (a x : ℕ) (h : a + 1 ≤ 32) : unitPt (a + 1) x ^ 2 = unitPt a (x / 2) := by
  unfold unitPt
  rw [← pow_mul]
  show rootW ^ (((if x.testBit 0 = true then 2 ^ (32 - (0 + 1)) else 0) + expFrom x a (0 + 1)) * 2)
    = rootW ^ expFrom (x / 2) a 0
  rw [Nat.add_mul, Nat.mul_comm (expFrom x a (0 + 1)) 2, two_mul_expFrom x a 0 (by omega), pow_add]
  by_cases hb : x.testBit 0 = true
  · rw [if_pos hb]
    have h2 : (2 : ℕ) ^ (32 - (0 + 1)) * 2 = 2 ^ (31 + 1) := by norm_num
    rw [h2, rootW_pow_top, one_mul]
  · rw [if_neg hb, Nat.zero_mul, pow_zero, one_mul]

/-- The power 2^k of a point of a domain of length 2^(b + k) is the point of the position divided by
2^k in the domain of length 2^b. -/
theorem unitPt_pow (b k x : ℕ) (h : b + k ≤ 32) :
    unitPt (b + k) x ^ 2 ^ k = unitPt b (x / 2 ^ k) := by
  induction k generalizing x with
  | zero => rw [pow_zero, pow_one, Nat.div_one, Nat.add_zero]
  | succ k ih =>
    rw [pow_succ' 2 k, pow_mul, ← Nat.add_assoc, unitPt_sq (b + k) x (by omega),
      ih (x / 2) (by omega), Nat.div_div_eq_div_mul]

/-- For a up to 32, positions below 2^a with the same point are the same. -/
theorem unitPt_inj (a : ℕ) (ha : a ≤ 32) {x y : ℕ} (hx : x < 2 ^ a) (hy : y < 2 ^ a)
    (h : unitPt a x = unitPt a y) : x = y :=
  toF_point_inj a ha hx hy (by rw [toF_point_unit, toF_point_unit, h])

/-- A position below 2^(b + k) with its two parts exchanged: the b low bits go to the top, the k
high bits to the bottom. -/
def turn (b k x : ℕ) : ℕ := x % 2 ^ b * 2 ^ k + x / 2 ^ b

/-- The high part of a position below 2^(b + k) is below 2^k. -/
theorem div_lt_of_lt_pow (b k x : ℕ) (hx : x < 2 ^ (b + k)) : x / 2 ^ b < 2 ^ k :=
  Nat.div_lt_of_lt_mul (by rwa [← pow_add])

/-- The turned position, divided by 2^k, is the position modulo 2^b. -/
theorem turn_div (b k x : ℕ) (hx : x < 2 ^ (b + k)) : turn b k x / 2 ^ k = x % 2 ^ b := by
  unfold turn
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k),
    Nat.div_eq_of_lt (div_lt_of_lt_pow b k x hx), Nat.zero_add]

/-- The turned position, modulo 2^k, is the position divided by 2^b. -/
theorem turn_mod (b k x : ℕ) (hx : x < 2 ^ (b + k)) : turn b k x % 2 ^ k = x / 2 ^ b := by
  unfold turn
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (div_lt_of_lt_pow b k x hx)]

/-- The turned position is below 2^(b + k). -/
theorem turn_lt (b k x : ℕ) (hx : x < 2 ^ (b + k)) : turn b k x < 2 ^ (b + k) := by
  have h1 : x % 2 ^ b < 2 ^ b := Nat.mod_lt _ (Nat.two_pow_pos b)
  have h2 := div_lt_of_lt_pow b k x hx
  unfold turn
  calc x % 2 ^ b * 2 ^ k + x / 2 ^ b < x % 2 ^ b * 2 ^ k + 2 ^ k := Nat.add_lt_add_left h2 _
    _ = (x % 2 ^ b + 1) * 2 ^ k := by rw [Nat.add_mul, Nat.one_mul]
    _ ≤ 2 ^ b * 2 ^ k := Nat.mul_le_mul_right _ h1
    _ = 2 ^ (b + k) := (pow_add 2 b k).symm

/-- Different positions below 2^(b + k) are turned into different positions. -/
theorem turn_inj (b k : ℕ) {x y : ℕ} (hx : x < 2 ^ (b + k)) (hy : y < 2 ^ (b + k))
    (h : turn b k x = turn b k y) : x = y := by
  have h1 : x % 2 ^ b = y % 2 ^ b := by rw [← turn_div b k x hx, ← turn_div b k y hy, h]
  have h2 : x / 2 ^ b = y / 2 ^ b := by rw [← turn_mod b k x hx, ← turn_mod b k y hy, h]
  rw [← Nat.div_add_mod x (2 ^ b), ← Nat.div_add_mod y (2 ^ b), h1, h2]

end OnBytes.Slice
