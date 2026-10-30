-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Ent/CdPoints.lean: facts on the evaluation points of Cb/Ent/CdPts.lean.

Main names:
  `rootW_order`: w has order exactly 2^32 (two evaluations by the kernel).
  `pt_eq`, `pt_inj`, `ptOf_inj`: for a ≤ 32 the 2^a points of a code are different.
  `unitPt`, `pt_unit`, `unitPt_sq`, `unitPt_pow`, `unitPt_inj`: the points without the factor 7; the
    square of the point of x at length 2^(a + 1) is the point of x / 2 at length 2^a.
  `turn` with `turn_div`, `turn_mod`, `turn_lt`, `turn_inj`: the renumbering of positions under
    which a code repeated to a longer tree lies in a Reed-Solomon code at the longer tree's points.

Limits: beyond a = 32 nothing is shown. Three proofs use "decide +kernel" on closed numbers.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ent.CdLink

set_option autoImplicit false

namespace Cb.Ent
open Code

/-- The constant, written as a number. -/
theorem rootW_eq : rootW = ((16334397945464290598 : ℕ) : Cb.Gl.F) := rfl

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

/-- The factor 7 is not 0. -/
theorem gen7_ne_zero : gen7 ≠ 0 := by
  show ((7 : ℕ) : Cb.Gl.F) ≠ 0
  exact natCast_ne_zero_of_lt FGold pGold (by norm_num) (by decide +kernel)

/-- The point of x is 7 times the constant to the power `expFrom x a 0`. -/
theorem pt_eq (a x : ℕ) : pt a x = gen7 * rootW ^ expFrom x a 0 := rfl

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

/-- For a up to 32, positions below 2^a with the same point are the same. -/
theorem pt_inj (a : ℕ) (ha : a ≤ 32) {x y : ℕ} (hx : x < 2 ^ a) (hy : y < 2 ^ a)
    (h : pt a x = pt a y) : x = y := by
  rw [pt_eq, pt_eq] at h
  have h1 : rootW ^ expFrom x a 0 = rootW ^ expFrom y a 0 :=
    mul_left_cancel₀ gen7_ne_zero h
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
  fun x y h => Fin.ext (pt_inj a ha x.isLt y.isLt h)

end Cb.Ent

namespace Cb.Ent

/-- The point of x in a code of length 2^a, without the factor 7. -/
def unitPt (a x : ℕ) : Cb.Gl.F := rootW ^ expFrom x a 0

/-- The point of x is 7 times `unitPt a x`. -/
theorem pt_unit (a x : ℕ) : pt a x = gen7 * unitPt a x := pt_eq a x

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
  pt_inj a ha hx hy (by rw [pt_unit, pt_unit, h])

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

end Cb.Ent
