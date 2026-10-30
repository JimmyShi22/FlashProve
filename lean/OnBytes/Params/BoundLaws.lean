-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/BoundLaws.lean: each operation on the planner's intervals, but the square root, keeps
the true value between the ends, unless it marks the result bad.

OnBytes/Params/Real.lean has numbers m * 2 ^ e (`Binary`) and pairs of them around a true value
(`Bound`), with a mark `bad`. OnBytes/Params/RealLaws.lean gives a number its value and treats cut,
`le`, and sum and product upward. This file adds `lt`, sum and product downward, difference,
quotient, power and floor, and then says of each operation on bounds but `sqrt`: if the arguments
enclose x and y, and the result is not marked bad, the result encloses the operation's true value on
x and y. So in a formula made of these operations one mark is to be looked at: the last result's.

Main definition: `Encl`.
Main theorems, in the namespace `Binary`: `lt_sound`, `val_sub_down`, `val_sub_up`, `val_div_down`,
`val_div_up`, `val_pow_up`, `val_pow_down`, `floor_le`, `lt_floor`. In the namespace `Bound`:
`encl_ofNat`, `encl_add`, `encl_sub`, `encl_mul`, `encl_div`, `encl_ratio`, `encl_pow`, `le_error`.
What is not claimed: nothing on `sqrt`, `isqrt`, `ceil`, `surelyLe`; `surelyLt` is in
OnBytes/Params/GroupPrices.lean. Nothing on a bound that is marked bad. When a sum, a product or a
power is marked bad is in OnBytes/Params/CmpLaws.lean; nothing on when another result is. Nothing on
how near the two ends lie to each other. That `lt` says yes of all numbers in that order is in
OnBytes/Params/CmpLaws.lean. A bound whose ends have crossed and that is not marked bad encloses no
number: of such an argument nothing is said. That a plan within a third of the distance takes no
square root: that is read off `atDistance` (OnBytes/Params/Distance.lean), and no theorem states it.
Nothing on any formula of the planner. Nothing on the C++ arithmetic, of which
OnBytes/Params/Real.lean is a rendering. For proofs only; the program, that is the Lean port built
from OnBytes/, does not import this file.

-/
import OnBytes.Params.RealLaws

set_option autoImplicit false

namespace OnBytes.Params
namespace Binary

/-- A power of two is above 0. -/
theorem two_zpow_pos (e : ℤ) : (0 : ℚ) < (2 : ℚ) ^ e := zpow_pos (by norm_num) _

/-- A number whose m is 0 has the value 0. -/
theorem val_of_isZero (a : Binary) (h : a.isZero = true) : a.val = 0 := by
  have : a.m = 0 := by simpa [isZero] using h
  simp [val, this]

/-- A number whose m is not 0 has a value above 0. -/
theorem val_pos (a : Binary) (h : a.isZero = false) : 0 < a.val := by
  have : a.m ≠ 0 := by simpa [isZero] using h
  exact mul_pos (by exact_mod_cast Nat.pos_of_ne_zero this) (two_zpow_pos _)

/-- A product that is rounded down is at most the product. -/
theorem val_mul_down (a b : Binary) : (a.mul b .down).val ≤ a.val * b.val := by
  refine le_trans (val_cut_down _) (le_of_eq ?_)
  show ((a.m * b.m : ℕ) : ℚ) * 2 ^ (a.e + b.e) = (a.m : ℚ) * 2 ^ a.e * ((b.m : ℚ) * 2 ^ b.e)
  rw [zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  push_cast
  ring

/-- A sum that is rounded down is at most the sum. -/
theorem val_add_down (a b : Binary) : (a.add b .down).val ≤ a.val + b.val := by
  unfold add
  split
  · rename_i h
    rw [val_of_isZero a h, zero_add]
  · split
    · rename_i h
      rw [val_of_isZero b h, add_zero]
    · refine le_trans (val_cut_down _) (le_of_eq ?_)
      show ((a.m * 2 ^ (a.e - min a.e b.e).toNat + b.m * 2 ^ (b.e - min a.e b.e).toNat : ℕ) : ℚ) *
          2 ^ (min a.e b.e) = (a.m : ℚ) * 2 ^ a.e + (b.m : ℚ) * 2 ^ b.e
      rw [Nat.cast_add, add_mul, val_lower _ _ _ (min_le_left _ _),
        val_lower _ _ _ (min_le_right _ _)]

/-- `lt` says yes only of numbers in that strict order. -/
theorem lt_sound (a b : Binary) (h : a.lt b = true) : a.val < b.val := by
  unfold lt cmp at h
  simp only [beq_iff_eq] at h
  split at h
  · split at h
    · rename_i _ ha
      split at h
      · cases h
      · rename_i hb
        rw [val_of_isZero a ha]
        exact val_pos b (by simpa using hb)
    · cases h
  · rename_i hz
    have hb : b.m ≠ 0 := by
      intro h0
      apply hz
      simp [isZero, h0]
    split at h
    · split at h
      · rename_i _ hlt
        have h1 : (2 : ℚ) ^ a.top ≤ (2 : ℚ) ^ (b.top - 1) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        exact ((val_lt_top a).trans_le h1).trans_le (top_le_val b hb)
      · cases h
    · split at h
      · rename_i he
        have hn : a.m * 2 ^ (a.e - b.e).toNat < b.m := Nat.compare_eq_lt.1 h
        show (a.m : ℚ) * 2 ^ a.e < (b.m : ℚ) * 2 ^ b.e
        rw [← val_lower a.m a.e b.e he]
        exact mul_lt_mul_of_pos_right (by exact_mod_cast hn) (two_zpow_pos _)
      · rename_i he
        have hn : a.m < b.m * 2 ^ (b.e - a.e).toNat := Nat.compare_eq_lt.1 h
        show (a.m : ℚ) * 2 ^ a.e < (b.m : ℚ) * 2 ^ b.e
        rw [← val_lower b.m b.e a.e (by omega)]
        exact mul_lt_mul_of_pos_right (by exact_mod_cast hn) (two_zpow_pos _)

/-- The difference before the cut, for b at most a. -/
theorem val_sub_raw (a b : Binary) (h : b.val ≤ a.val) :
    ((a.m * 2 ^ (a.e - min a.e b.e).toNat - b.m * 2 ^ (b.e - min a.e b.e).toNat : ℕ) : ℚ) *
      2 ^ (min a.e b.e) = a.val - b.val := by
  have ha := val_lower a.m a.e (min a.e b.e) (min_le_left _ _)
  have hb := val_lower b.m b.e (min a.e b.e) (min_le_right _ _)
  have hle : b.m * 2 ^ (b.e - min a.e b.e).toNat ≤ a.m * 2 ^ (a.e - min a.e b.e).toNat := by
    have h' : ((b.m * 2 ^ (b.e - min a.e b.e).toNat : ℕ) : ℚ) * 2 ^ (min a.e b.e) ≤
        ((a.m * 2 ^ (a.e - min a.e b.e).toNat : ℕ) : ℚ) * 2 ^ (min a.e b.e) := by
      rw [ha, hb]
      exact h
    exact_mod_cast le_of_mul_le_mul_right h' (two_zpow_pos _)
  rw [Nat.cast_sub hle, sub_mul, ha, hb]
  rfl

/-- A difference that is rounded down is at most the difference, for b at most a. -/
theorem val_sub_down (a b : Binary) (h : b.val ≤ a.val) :
    (a.sub b .down).val ≤ a.val - b.val := by
  unfold sub
  split
  · rename_i hz
    rw [val_of_isZero b hz, sub_zero]
  · exact le_trans (val_cut_down _) (le_of_eq (val_sub_raw a b h))

/-- A difference that is rounded up is at least the difference, for b at most a. -/
theorem val_sub_up (a b : Binary) (h : b.val ≤ a.val) :
    a.val - b.val ≤ (a.sub b .up).val := by
  unfold sub
  split
  · rename_i hz
    rw [val_of_isZero b hz, sub_zero]
  · exact le_trans (le_of_eq (val_sub_raw a b h).symm) (val_cut_up _)

/-- The true quotient, with the dividend shifted up by s digits. -/
theorem val_div_raw (a b : Binary) (hb : b.m ≠ 0) (s : ℕ) :
    a.val / b.val = ((a.m * 2 ^ s : ℕ) : ℚ) / (b.m : ℚ) * 2 ^ (a.e - s - b.e) := by
  have hbm : (b.m : ℚ) ≠ 0 := by exact_mod_cast hb
  have h2 : (2 : ℚ) ≠ 0 := by norm_num
  unfold val
  rw [zpow_sub₀ h2, zpow_sub₀ h2, zpow_natCast]
  have p1 : (2 : ℚ) ^ b.e ≠ 0 := (two_zpow_pos _).ne'
  have p2 : (2 : ℚ) ^ s ≠ 0 := by positivity
  push_cast
  field_simp

/-- A quotient that is rounded down is at most the quotient, for a divisor other than 0. -/
theorem val_div_down (a b : Binary) (hb : b.m ≠ 0) : (a.div b .down).val ≤ a.val / b.val := by
  unfold div
  split
  · rename_i hz
    rw [val_of_isZero a hz, zero_div]
  · dsimp only
    generalize realBits + 2 + bitsOf b.m = s
    refine le_trans (val_cut_down _) ?_
    rw [val_div_raw a b hb s]
    have hf : (Dir.down == Dir.up && a.m * 2 ^ s % b.m != 0) = false := rfl
    rw [if_neg (by rw [hf]; exact Bool.false_ne_true)]
    show ((a.m * 2 ^ s / b.m : ℕ) : ℚ) * 2 ^ (a.e - s - b.e) ≤ _
    refine mul_le_mul_of_nonneg_right ?_ (two_zpow_pos _).le
    exact Nat.cast_div_le

/-- A quotient that is rounded up is at least the quotient, for a divisor other than 0. -/
theorem val_div_up (a b : Binary) (hb : b.m ≠ 0) : a.val / b.val ≤ (a.div b .up).val := by
  unfold div
  split
  · rename_i hz
    rw [val_of_isZero a hz, zero_div]
  · dsimp only
    generalize realBits + 2 + bitsOf b.m = s
    refine le_trans ?_ (val_cut_up _)
    rw [val_div_raw a b hb s]
    have hbq : (0 : ℚ) < (b.m : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hb
    generalize a.m * 2 ^ s = x
    split
    · show (x : ℚ) / (b.m : ℚ) * 2 ^ (a.e - s - b.e) ≤ ((x / b.m + 1 : ℕ) : ℚ) * 2 ^ (a.e - s - b.e)
      refine mul_le_mul_of_nonneg_right ?_ (two_zpow_pos _).le
      rw [div_le_iff₀ hbq]
      have h1 : x < b.m * (x / b.m + 1) := Nat.lt_mul_div_succ x (Nat.pos_of_ne_zero hb)
      rw [Nat.mul_comm] at h1
      exact_mod_cast h1.le
    · rename_i hn
      have hz : x % b.m = 0 := by
        by_contra hne
        apply hn
        show (Dir.up == Dir.up && x % b.m != 0) = true
        simp [hne]
      show (x : ℚ) / (b.m : ℚ) * 2 ^ (a.e - s - b.e) ≤ ((x / b.m : ℕ) : ℚ) * 2 ^ (a.e - s - b.e)
      refine mul_le_mul_of_nonneg_right ?_ (two_zpow_pos _).le
      rw [Nat.cast_div (Nat.dvd_of_mod_eq_zero hz) hbq.ne']

/-- A natural number lies below two to the number of its digits. -/
theorem nat_lt_two_bits (n : ℕ) : n < 2 ^ bitsOf n := by
  unfold bitsOf
  split
  · rename_i h
    have : n = 0 := by simpa using h
    simp [this]
  · exact Nat.lt_log2_self

/-- The exponent n, split as the steps of a power by squaring split it. -/
theorem pow_split (x : ℚ) (n : ℕ) : x ^ n = x ^ (n % 2) * (x ^ 2) ^ (n / 2) := by
  rw [← pow_mul, ← pow_add]
  congr 1
  omega

/-- The steps of a power by squaring, rounded up, with fuel enough (n < 2 ^ fuel): the result is at
least r * a ^ n. With less fuel the steps end early, and the result can lie below. -/
theorem val_powFrom_up : ∀ (fuel : ℕ) (r a : Binary) (n : ℕ), n < 2 ^ fuel →
    r.val * a.val ^ n ≤ (powFrom .up fuel r a n).val
  | 0, r, a, n, h => by
      have h0 : n = 0 := by simpa using h
      subst h0
      simp [powFrom]
  | fuel + 1, r, a, n, h => by
      unfold powFrom
      split
      · rename_i h0
        have h0' : n = 0 := by simpa using h0
        subst h0'
        simp
      · dsimp only
        have hn2 : n / 2 < 2 ^ fuel := by
          rw [pow_succ] at h
          omega
        refine le_trans ?_ (val_powFrom_up fuel _ _ (n / 2) hn2)
        have hr' : r.val * a.val ^ (n % 2) ≤ (if n % 2 == 1 then mul r a .up else r).val := by
          split
          · rename_i h1
            have h1' : n % 2 = 1 := by simpa using h1
            rw [h1', pow_one]
            exact val_mul_up r a
          · rename_i h1
            have h1' : n % 2 = 0 := by
              have h2 : ¬ n % 2 = 1 := by simpa using h1
              omega
            rw [h1', pow_zero, mul_one]
        have ha' : (a.val ^ 2) ^ (n / 2) ≤ (if 1 < n then mul a a .up else a).val ^ (n / 2) := by
          split
          · refine pow_le_pow_left₀ (pow_nonneg (val_nonneg a) _) ?_ _
            rw [pow_two]
            exact val_mul_up a a
          · rename_i h1
            have h1' : n / 2 = 0 := by omega
            rw [h1', pow_zero, pow_zero]
        rw [pow_split a.val n, ← mul_assoc]
        exact mul_le_mul hr' ha' (pow_nonneg (pow_nonneg (val_nonneg a) _) _) (val_nonneg _)

/-- The steps of a power by squaring, rounded down, with fuel enough (n < 2 ^ fuel): the result is
at most r * a ^ n. With less fuel the steps end early, and the result can lie above. -/
theorem val_powFrom_down : ∀ (fuel : ℕ) (r a : Binary) (n : ℕ), n < 2 ^ fuel →
    (powFrom .down fuel r a n).val ≤ r.val * a.val ^ n
  | 0, r, a, n, h => by
      have h0 : n = 0 := by simpa using h
      subst h0
      simp [powFrom]
  | fuel + 1, r, a, n, h => by
      unfold powFrom
      split
      · rename_i h0
        have h0' : n = 0 := by simpa using h0
        subst h0'
        simp
      · dsimp only
        have hn2 : n / 2 < 2 ^ fuel := by
          rw [pow_succ] at h
          omega
        refine le_trans (val_powFrom_down fuel _ _ (n / 2) hn2) ?_
        have hr' : (if n % 2 == 1 then mul r a .down else r).val ≤ r.val * a.val ^ (n % 2) := by
          split
          · rename_i h1
            have h1' : n % 2 = 1 := by simpa using h1
            rw [h1', pow_one]
            exact val_mul_down r a
          · rename_i h1
            have h1' : n % 2 = 0 := by
              have h2 : ¬ n % 2 = 1 := by simpa using h1
              omega
            rw [h1', pow_zero, mul_one]
        have ha' : (if 1 < n then mul a a .down else a).val ^ (n / 2) ≤ (a.val ^ 2) ^ (n / 2) := by
          split
          · refine pow_le_pow_left₀ (val_nonneg _) ?_ _
            rw [pow_two]
            exact val_mul_down a a
          · rename_i h1
            have h1' : n / 2 = 0 := by omega
            rw [h1', pow_zero, pow_zero]
        rw [pow_split a.val n, ← mul_assoc]
        exact mul_le_mul hr' ha' (pow_nonneg (val_nonneg _) _)
          (mul_nonneg (val_nonneg _) (pow_nonneg (val_nonneg a) _))

/-- A power that is rounded up is at least the power. -/
theorem val_pow_up (a : Binary) (n : ℕ) : a.val ^ n ≤ (a.pow n .up).val := by
  have h := val_powFrom_up (bitsOf n) (ofNat 1) a n (nat_lt_two_bits n)
  rw [val_ofNat, Nat.cast_one, one_mul] at h
  exact h

/-- A power that is rounded down is at most the power. -/
theorem val_pow_down (a : Binary) (n : ℕ) : (a.pow n .down).val ≤ a.val ^ n := by
  have h := val_powFrom_down (bitsOf n) (ofNat 1) a n (nat_lt_two_bits n)
  rw [val_ofNat, Nat.cast_one, one_mul] at h
  exact h

/-- The value with a negative exponent, as a quotient. -/
theorem val_of_neg (a : Binary) (h : ¬ 0 ≤ a.e) :
    a.val = (a.m : ℚ) / ((2 ^ (-a.e).toNat : ℕ) : ℚ) := by
  have e : a.e = -(((-a.e).toNat : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  show (a.m : ℚ) * (2 : ℚ) ^ a.e = _
  rw [e, zpow_neg, zpow_natCast, div_eq_mul_inv]
  push_cast
  rw [Int.toNat_of_nonneg (by omega)]
  simp

/-- The floor is at most the value. -/
theorem floor_le (a : Binary) : (a.floor : ℚ) ≤ a.val := by
  unfold floor
  split
  · rename_i h
    have := val_lower a.m a.e 0 h
    rw [zpow_zero, mul_one, sub_zero] at this
    exact this.le
  · rename_i h
    rw [val_of_neg a h]
    exact Nat.cast_div_le

/-- The value lies below the floor and one. -/
theorem lt_floor (a : Binary) : a.val < (a.floor : ℚ) + 1 := by
  unfold floor
  split
  · rename_i h
    have := val_lower a.m a.e 0 h
    rw [zpow_zero, mul_one, sub_zero] at this
    rw [this]
    show (a.m : ℚ) * 2 ^ a.e < (a.m : ℚ) * 2 ^ a.e + 1
    linarith
  · rename_i h
    rw [val_of_neg a h]
    generalize (-a.e).toNat = k
    have hP : 0 < 2 ^ k := Nat.pos_of_ne_zero (by positivity)
    have hPq : (0 : ℚ) < ((2 ^ k : ℕ) : ℚ) := by exact_mod_cast hP
    rw [div_lt_iff₀ hPq]
    have h1 : a.m < 2 ^ k * (a.m / 2 ^ k + 1) := Nat.lt_mul_div_succ a.m hP
    rw [Nat.mul_comm] at h1
    exact_mod_cast h1

end Binary

/-- The bound b encloses x, unless b is marked bad. -/
def Encl (b : Bound) (x : ℚ) : Prop := b.bad = false → b.lo.val ≤ x ∧ x ≤ b.hi.val

namespace Bound
open Binary

/-- An exact bound encloses its number's value. -/
theorem encl_exact (a : Binary) : Encl (exact a) a.val := fun _ => ⟨le_rfl, le_rfl⟩

/-- `ofWord x` encloses x. -/
theorem encl_ofWord (x : ℕ) : Encl (ofWord x) x := by
  have h := encl_exact (Binary.ofNat x)
  rw [val_ofNat] at h
  exact h

/-- `ofNat x` encloses x. -/
theorem encl_ofNat (x : ℕ) : Encl (ofNat x) x := fun _ => by
  have h1 := val_cut_down (Binary.ofNat x)
  have h2 := val_cut_up (Binary.ofNat x)
  rw [val_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- What a result's mark says of the arguments' marks, for `inherit`. -/
theorem inherit_good {r a b : Bound} (h : (r.inherit a b).bad = false) :
    a.bad = false ∧ b.bad = false := by
  have h' : (r.bad || a.bad || b.bad) = false := h
  simp only [Bool.or_eq_false_iff] at h'
  exact ⟨h'.1.2, h'.2⟩

/-- The sum of two bounds, where it is not marked bad, encloses the sum. -/
theorem encl_add {a b : Bound} {x y : ℚ} (ha : Encl a x) (hb : Encl b y) :
    Encl (a + b) (x + y) := fun h => by
  obtain ⟨g1, g2⟩ := inherit_good (r := ends (a.lo.add b.lo .down) (a.hi.add b.hi .up)) h
  obtain ⟨a1, a2⟩ := ha g1
  obtain ⟨b1, b2⟩ := hb g2
  exact ⟨(val_add_down _ _).trans (add_le_add a1 b1), (add_le_add a2 b2).trans (val_add_up _ _)⟩

/-- The product of two bounds, where it is not marked bad, encloses the product. -/
theorem encl_mul {a b : Bound} {x y : ℚ} (ha : Encl a x) (hb : Encl b y) :
    Encl (a * b) (x * y) := fun h => by
  obtain ⟨g1, g2⟩ := inherit_good (r := ends (a.lo.mul b.lo .down) (a.hi.mul b.hi .up)) h
  obtain ⟨a1, a2⟩ := ha g1
  obtain ⟨b1, b2⟩ := hb g2
  have x0 : 0 ≤ x := (val_nonneg _).trans a1
  have y0 : 0 ≤ y := (val_nonneg _).trans b1
  exact ⟨(val_mul_down _ _).trans (mul_le_mul a1 b1 (val_nonneg _) x0),
    (mul_le_mul a2 b2 y0 (val_nonneg _)).trans (val_mul_up _ _)⟩

/-- The power of a bound, where it is not marked bad, encloses the power. -/
theorem encl_pow {a : Bound} {x : ℚ} (ha : Encl a x) (n : ℕ) : Encl (a.pow n) (x ^ n) := fun h => by
  obtain ⟨g1, _⟩ := inherit_good (r := ends (a.lo.pow n .down) (a.hi.pow n .up)) h
  obtain ⟨a1, a2⟩ := ha g1
  have x0 : 0 ≤ x := (val_nonneg _).trans a1
  exact ⟨(val_pow_down _ _).trans (pow_le_pow_left₀ (val_nonneg _) a1 n),
    (pow_le_pow_left₀ x0 a2 n).trans (val_pow_up _ _)⟩

/-- The difference of two bounds, where it is not marked bad, encloses the difference. -/
theorem encl_sub {a b : Bound} {x y : ℚ} (ha : Encl a x) (hb : Encl b y) :
    Encl (a - b) (x - y) := fun h => by
  have h' : (Bound.sub a b).bad = false := h
  show (Bound.sub a b).lo.val ≤ x - y ∧ x - y ≤ (Bound.sub a b).hi.val
  unfold Bound.sub at h' ⊢
  split at h'
  · cases h'
  · rename_i hc
    rw [if_neg hc]
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_true,
      Bool.not_eq_false] at hc
    obtain ⟨⟨g1, g2⟩, g3⟩ := hc
    obtain ⟨a1, a2⟩ := ha g1
    obtain ⟨b1, b2⟩ := hb g2
    have hlt := lt_sound _ _ g3
    exact ⟨(val_sub_down _ _ hlt.le).trans (by linarith),
      le_trans (by linarith) (val_sub_up _ _ (by linarith))⟩

/-- The quotient of two bounds, where it is not marked bad, encloses the quotient. -/
theorem encl_div {a b : Bound} {x y : ℚ} (ha : Encl a x) (hb : Encl b y) :
    Encl (a / b) (x / y) := fun h => by
  have h' : (Bound.div a b).bad = false := h
  show (Bound.div a b).lo.val ≤ x / y ∧ x / y ≤ (Bound.div a b).hi.val
  unfold Bound.div at h' ⊢
  split at h'
  · cases h'
  · rename_i hc
    rw [if_neg hc]
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
    obtain ⟨⟨g1, g2⟩, g3⟩ := hc
    obtain ⟨a1, a2⟩ := ha g1
    obtain ⟨b1, b2⟩ := hb g2
    have l0 : 0 < b.lo.val := val_pos _ g3
    have y0 : 0 < y := l0.trans_le b1
    have h0 : 0 < b.hi.val := y0.trans_le b2
    have x0 : 0 ≤ x := (val_nonneg _).trans a1
    have hlom : b.lo.m ≠ 0 := by simpa [isZero] using g3
    have hhim : b.hi.m ≠ 0 := by
      intro hz
      have : b.hi.val = 0 := by simp [val, hz]
      linarith
    exact ⟨(val_div_down _ _ hhim).trans (div_le_div₀ x0 a1 y0 b2),
      (div_le_div₀ (val_nonneg _) a2 l0 b1).trans (val_div_up _ _ hlom)⟩

/-- `ratio a b`, where it is not marked bad, encloses a / b. -/
theorem encl_ratio (a b : ℕ) : Encl (ratio a b) ((a : ℚ) / (b : ℚ)) :=
  encl_div (encl_ofNat a) (encl_ofNat b)

/-- The upper end of a bound that is not bad, as `error` returns it, is at least what the bound
encloses. -/
theorem le_error {b : Bound} {x : ℚ} (hb : Encl b x) (h : b.bad = false) : x ≤ b.error.val := by
  unfold error
  rw [h]
  exact (hb h).2

end Bound
end OnBytes.Params

#print axioms OnBytes.Params.Binary.lt_sound
#print axioms OnBytes.Params.Binary.val_sub_down
#print axioms OnBytes.Params.Binary.val_sub_up
#print axioms OnBytes.Params.Binary.val_div_down
#print axioms OnBytes.Params.Binary.val_div_up
#print axioms OnBytes.Params.Binary.val_pow_up
#print axioms OnBytes.Params.Binary.val_pow_down
#print axioms OnBytes.Params.Binary.floor_le
#print axioms OnBytes.Params.Binary.lt_floor
#print axioms OnBytes.Params.Bound.encl_add
#print axioms OnBytes.Params.Bound.encl_sub
#print axioms OnBytes.Params.Bound.encl_mul
#print axioms OnBytes.Params.Bound.encl_div
#print axioms OnBytes.Params.Bound.encl_ratio
#print axioms OnBytes.Params.Bound.encl_pow
