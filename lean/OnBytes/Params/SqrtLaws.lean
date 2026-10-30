-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/SqrtLaws.lean: the planner's square root encloses the square root; and the planner's
intervals over the real numbers.

OnBytes/Params/BoundLaws.lean proves of each operation on the planner's intervals, but the square
root, that it keeps a rational number between the ends. This file adds the square root. The
planner's integer square root is Newton's iteration from above with fuel. A step from a number above
0 does not fall below the root (`sqrt_le_step`), and above the root it at least halves the distance
to it (`step_le_half`), so the fuel is enough: what `isqrt a` returns is `Nat.sqrt a`, the root
rounded down (`isqrtFrom_eq`, `isqrt_eq`). That the iteration stops before the fuel ends is not
stated. `Binary.sqrt` shifts the number's digits up, by a number of digits that makes the exponent
even (`sqrt_shift`), takes that root, and cuts toward the side asked: the square of the root rounded
down is at most the number, and the square of the root rounded up is at least the number
(`val_sqrt_down`, `val_sqrt_up`). A square root is as a rule not rational, so enclosing is said over
the real numbers: `EnclR b x` says that the bound b, unless it is marked bad, has the real number x
between its ends. The square root of a bound encloses the square root of what the bound encloses
(`enclR_sqrt`; in squares: `sqrt_sq`). The other operations enclose over the real numbers as they do
over the rational ones (`enclR_of_encl`, `enclR_ofWord`, `enclR_ofNat`, `enclR_ratio`, `enclR_add`,
`enclR_mul`, `enclR_pow`, `enclR_sub`, `enclR_div`), and `error` returns at least what a bound that
is not bad encloses (`le_errorR`).

Main definition: `EnclR`.
Main theorems: `sqrt_le_step`, `step_le_half`, `isqrtFrom_eq`, `isqrt_eq`, `Binary.val_sq_even`,
`Binary.sqrt_shift`, `Binary.val_sqrt_down`, `Binary.val_sqrt_up`, `Bound.enclR_of_encl`,
`Bound.sqrt_sq`, `Bound.enclR_sqrt`, `Bound.enclR_ofWord`, `Bound.enclR_ofNat`, `Bound.enclR_ratio`,
`Bound.enclR_nonneg`, `Bound.enclR_add`, `Bound.enclR_mul`, `Bound.enclR_pow`, `Bound.enclR_sub`,
`Bound.enclR_div`, `Bound.le_errorR`.
What is not claimed: how narrow an interval is. That a result is not marked bad. Anything on the
planner's formulas that use the square root (the distance, the count and the list up to the Johnson
radius, OnBytes/Params/Distance.lean): no formula is shown here to enclose a number. Nothing on the
C++ planner's square root. For proofs only; the program, that is the Lean port built from OnBytes/,
does not import this file.

-/
import OnBytes.Params.BoundLaws
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false

namespace OnBytes.Params

/-- A step of Newton's iteration from a number above 0 does not fall below the root. -/
theorem sqrt_le_step (a x : ℕ) (hx : 0 < x) : Nat.sqrt a ≤ (x + a / x) / 2 := by
  set s := Nat.sqrt a with hs
  have hss : s * s ≤ a := Nat.sqrt_le a
  rw [Nat.le_div_iff_mul_le (by norm_num)]
  by_cases h : 2 * s ≤ x
  · exact le_trans (by omega) (Nat.le_add_right x (a / x))
  · have h' : x < 2 * s := Nat.lt_of_not_le h
    have key : (2 * s - x) * x ≤ a := by
      refine le_trans ?_ hss
      obtain ⟨d, hd⟩ : ∃ d, 2 * s = x + d := ⟨2 * s - x, by omega⟩
      have e : 2 * s - x = d := by omega
      rw [e]
      -- d * x ≤ s * s, where x + d = 2 s
      nlinarith [sq_nonneg ((x : ℤ) - (d : ℤ)), hd]
    have : 2 * s - x ≤ a / x := (Nat.le_div_iff_mul_le hx).mpr key
    omega

/-- Above the root a step at least halves the distance to the root. -/
theorem step_le_half (a x : ℕ) (hx : Nat.sqrt a < x) :
    (x + a / x) / 2 ≤ (x + Nat.sqrt a) / 2 := by
  have h1 : a < (Nat.sqrt a + 1) * (Nat.sqrt a + 1) := Nat.lt_succ_sqrt a
  have h2 : a / x ≤ Nat.sqrt a := by
    have : a / x < Nat.sqrt a + 1 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      calc a < (Nat.sqrt a + 1) * (Nat.sqrt a + 1) := h1
        _ ≤ (Nat.sqrt a + 1) * x := Nat.mul_le_mul_left _ (by omega)
    omega
  exact Nat.div_le_div_right (by omega)

/-- From a start that is not below the root, and with fuel for the halvings, the iteration ends at
the root. -/
theorem isqrtFrom_eq (a : ℕ) : ∀ (fuel x : ℕ), 0 < x → Nat.sqrt a ≤ x →
    x - Nat.sqrt a < 2 ^ fuel → isqrtFrom a fuel x = Nat.sqrt a
  | 0, x, _, h1, h2 => by
    simp only [pow_zero, Nat.lt_one_iff] at h2
    unfold isqrtFrom
    omega
  | fuel + 1, x, h0, h1, h2 => by
    unfold isqrtFrom
    simp only
    by_cases hx : Nat.sqrt a < x
    · have hy := step_le_half a x hx
      have hlt : ¬ x ≤ (x + a / x) / 2 := by omega
      rw [if_neg hlt]
      have hge := sqrt_le_step a x h0
      by_cases hz : (x + a / x) / 2 = 0
      · -- then the root is 0 and the next value is 0: the iteration stays there
        have hs0 : Nat.sqrt a = 0 := by omega
        rw [hz, hs0]
        cases fuel with
        | zero => rfl
        | succ n =>
          unfold isqrtFrom
          simp
      · refine isqrtFrom_eq a fuel _ (Nat.pos_of_ne_zero hz) hge ?_
        rw [pow_succ] at h2
        omega
    · have e : x = Nat.sqrt a := by omega
      have hge := sqrt_le_step a x h0
      rw [if_pos (by omega)]
      exact e

/-- **The planner's integer square root is the square root rounded down.** -/
theorem isqrt_eq (a : ℕ) : isqrt a = Nat.sqrt a := by
  unfold isqrt
  by_cases h : a = 0
  · simp [h]
  · have hb : (a == 0) = false := by simpa using h
    rw [hb]
    simp only [Bool.false_eq_true, if_false]
    have hlt : a < 2 ^ bitsOf a := Binary.nat_lt_two_bits a
    have hs : Nat.sqrt a < 2 ^ ((bitsOf a + 1) / 2) := by
      rw [Nat.sqrt_lt]
      calc a < 2 ^ bitsOf a := hlt
        _ ≤ 2 ^ ((bitsOf a + 1) / 2 + (bitsOf a + 1) / 2) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 ^ ((bitsOf a + 1) / 2) * 2 ^ ((bitsOf a + 1) / 2) := by rw [pow_add]
    refine isqrtFrom_eq a _ _ (by positivity) hs.le ?_
    calc 2 ^ ((bitsOf a + 1) / 2) - Nat.sqrt a ≤ 2 ^ ((bitsOf a + 1) / 2) := Nat.sub_le _ _
      _ < 2 ^ (bitsOf a + 8) := Nat.pow_lt_pow_right (by norm_num) (by omega)

namespace Binary

/-- The square of r * 2 ^ (e / 2), for an even e, is r * r * 2 ^ e. -/
theorem val_sq_even (r : ℕ) (e : ℤ) (he : e % 2 = 0) :
    ((⟨r, e / 2⟩ : Binary).val) ^ 2 = ((r * r : ℕ) : ℚ) * (2 : ℚ) ^ e := by
  obtain ⟨k, hk⟩ : ∃ k, e = 2 * k := ⟨e / 2, by omega⟩
  have h2 : e / 2 = k := by omega
  unfold val
  simp only [h2]
  rw [hk, two_mul, zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  push_cast
  ring

/-- What `sqrt` takes the root of: the number, with its digits shifted up so that the exponent is
even. -/
theorem sqrt_shift (a : Binary) :
    ∃ s : ℕ, (a.e - (s : ℤ)) % 2 = 0 ∧ a.val = ((a.m * 2 ^ s : ℕ) : ℚ) * (2 : ℚ) ^ (a.e - (s : ℤ)) ∧
      ∀ d, a.isZero = false → a.sqrt d =
        cut ⟨if d == .up && isqrt (a.m * 2 ^ s) * isqrt (a.m * 2 ^ s) != a.m * 2 ^ s
          then isqrt (a.m * 2 ^ s) + 1 else isqrt (a.m * 2 ^ s), (a.e - (s : ℤ)) / 2⟩ d := by
  refine ⟨if (a.e - ((2 * realBits + 4 : ℕ) : ℤ)) % 2 != 0 then 2 * realBits + 4 + 1
    else 2 * realBits + 4, ?_, ?_, ?_⟩
  · split
    · rename_i h
      simp only [bne_iff_ne, ne_eq] at h
      push_cast
      omega
    · rename_i h
      simp only [bne_iff_ne, ne_eq, not_not] at h
      exact h
  · rw [val_shift, sub_add_cancel]
    rfl
  · intro d hz
    unfold sqrt
    rw [hz]
    rfl

/-- **The square root rounded down: its square is at most the number.** -/
theorem val_sqrt_down (a : Binary) : ((a.sqrt .down).val) ^ 2 ≤ a.val := by
  by_cases hz : a.isZero = true
  · unfold sqrt
    rw [if_pos hz, val_of_isZero a hz]
    norm_num
  · have hz' : a.isZero = false := by simpa using hz
    obtain ⟨s, he, hv, hs⟩ := sqrt_shift a
    rw [hs .down hz']
    have hd : ((Dir.down == Dir.up) = false) := by decide
    simp only [hd, Bool.false_and, Bool.false_eq_true, if_false]
    have h1 := val_cut_down (⟨isqrt (a.m * 2 ^ s), (a.e - (s : ℤ)) / 2⟩ : Binary)
    have h0 := val_nonneg ((⟨isqrt (a.m * 2 ^ s), (a.e - (s : ℤ)) / 2⟩ : Binary).cut .down)
    calc _ ≤ ((⟨isqrt (a.m * 2 ^ s), (a.e - (s : ℤ)) / 2⟩ : Binary).val) ^ 2 :=
          pow_le_pow_left₀ h0 h1 2
      _ = ((isqrt (a.m * 2 ^ s) * isqrt (a.m * 2 ^ s) : ℕ) : ℚ) * (2 : ℚ) ^ (a.e - (s : ℤ)) :=
          val_sq_even _ _ he
      _ ≤ ((a.m * 2 ^ s : ℕ) : ℚ) * (2 : ℚ) ^ (a.e - (s : ℤ)) := by
          refine mul_le_mul_of_nonneg_right ?_ (two_zpow_pos _).le
          rw [isqrt_eq]
          exact_mod_cast Nat.sqrt_le (a.m * 2 ^ s)
      _ = a.val := hv.symm

/-- **The square root rounded up: its square is at least the number.** -/
theorem val_sqrt_up (a : Binary) : a.val ≤ ((a.sqrt .up).val) ^ 2 := by
  by_cases hz : a.isZero = true
  · unfold sqrt
    rw [if_pos hz, val_of_isZero a hz]
    norm_num
  · have hz' : a.isZero = false := by simpa using hz
    obtain ⟨s, he, hv, hs⟩ := sqrt_shift a
    rw [hs .up hz']
    set x := a.m * 2 ^ s with hx
    set r := if Dir.up == Dir.up && isqrt x * isqrt x != x then isqrt x + 1 else isqrt x with hr
    have hrx : x ≤ r * r := by
      rw [hr, isqrt_eq]
      split
      · exact (Nat.lt_succ_sqrt x).le
      · rename_i h
        simp only [beq_self_eq_true, Bool.true_and, bne_iff_ne, ne_eq, not_not] at h
        exact h.ge
    have h1 := val_cut_up (⟨r, (a.e - (s : ℤ)) / 2⟩ : Binary)
    have h0 := val_nonneg (⟨r, (a.e - (s : ℤ)) / 2⟩ : Binary)
    calc a.val = ((x : ℕ) : ℚ) * (2 : ℚ) ^ (a.e - (s : ℤ)) := hv
      _ ≤ ((r * r : ℕ) : ℚ) * (2 : ℚ) ^ (a.e - (s : ℤ)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hrx) (two_zpow_pos _).le
      _ = ((⟨r, (a.e - (s : ℤ)) / 2⟩ : Binary).val) ^ 2 := (val_sq_even _ _ he).symm
      _ ≤ _ := pow_le_pow_left₀ h0 h1 2

end Binary

/-- The bound b encloses the real number x, unless b is marked bad. -/
def EnclR (b : Bound) (x : ℝ) : Prop :=
  b.bad = false → ((b.lo.val : ℚ) : ℝ) ≤ x ∧ x ≤ ((b.hi.val : ℚ) : ℝ)

namespace Bound
open Binary

/-- A bound that encloses a rational number encloses it as a real number. -/
theorem enclR_of_encl {b : Bound} {x : ℚ} (h : Encl b x) : EnclR b (x : ℝ) := fun g =>
  ⟨by exact_mod_cast (h g).1, by exact_mod_cast (h g).2⟩

/-- **The square root of a bound, in squares**: where it is not marked bad, the square of its lower
end is at most what the bound encloses, and the square of its upper end is at least that. -/
theorem sqrt_sq {a : Bound} {x : ℝ} (ha : EnclR a x) (h : a.sqrt.bad = false) :
    (((a.sqrt.lo.val : ℚ) : ℝ)) ^ 2 ≤ x ∧ x ≤ (((a.sqrt.hi.val : ℚ) : ℝ)) ^ 2 := by
  obtain ⟨g1, _⟩ := inherit_good (r := ends (a.lo.sqrt .down) (a.hi.sqrt .up)) h
  obtain ⟨a1, a2⟩ := ha g1
  have l : (((a.lo.sqrt .down).val : ℚ) : ℝ) ^ 2 ≤ ((a.lo.val : ℚ) : ℝ) := by
    exact_mod_cast val_sqrt_down a.lo
  have u : ((a.hi.val : ℚ) : ℝ) ≤ (((a.hi.sqrt .up).val : ℚ) : ℝ) ^ 2 := by
    exact_mod_cast val_sqrt_up a.hi
  exact ⟨l.trans a1, a2.trans u⟩

/-- **The square root of a bound, where it is not marked bad, encloses the square root.** -/
theorem enclR_sqrt {a : Bound} {x : ℝ} (ha : EnclR a x) : EnclR a.sqrt (Real.sqrt x) := fun h => by
  obtain ⟨l, u⟩ := sqrt_sq ha h
  have l0 : (0 : ℝ) ≤ ((a.sqrt.lo.val : ℚ) : ℝ) := by exact_mod_cast val_nonneg a.sqrt.lo
  have u0 : (0 : ℝ) ≤ ((a.sqrt.hi.val : ℚ) : ℝ) := by exact_mod_cast val_nonneg a.sqrt.hi
  exact ⟨Real.le_sqrt_of_sq_le l, (Real.sqrt_le_left u0).mpr u⟩

/-- `ofWord x` encloses x. -/
theorem enclR_ofWord (x : ℕ) : EnclR (ofWord x) (x : ℝ) := by
  have h := enclR_of_encl (encl_ofWord x)
  simpa using h

/-- `ofNat x` encloses x. -/
theorem enclR_ofNat (x : ℕ) : EnclR (ofNat x) (x : ℝ) := by
  have h := enclR_of_encl (encl_ofNat x)
  simpa using h

/-- `ratio a b`, where it is not marked bad, encloses a / b. -/
theorem enclR_ratio (a b : ℕ) : EnclR (ratio a b) ((a : ℝ) / (b : ℝ)) := by
  have h := enclR_of_encl (encl_ratio a b)
  simpa using h

/-- What a bound that is not bad encloses is not negative. -/
theorem enclR_nonneg {a : Bound} {x : ℝ} (ha : EnclR a x) (g : a.bad = false) : 0 ≤ x :=
  le_trans (by exact_mod_cast val_nonneg a.lo) (ha g).1

/-- The sum of two bounds, where it is not marked bad, encloses the sum. -/
theorem enclR_add {a b : Bound} {x y : ℝ} (ha : EnclR a x) (hb : EnclR b y) :
    EnclR (a + b) (x + y) := fun h => by
  obtain ⟨g1, g2⟩ := inherit_good (r := ends (a.lo.add b.lo .down) (a.hi.add b.hi .up)) h
  obtain ⟨a1, a2⟩ := ha g1
  obtain ⟨b1, b2⟩ := hb g2
  have d : (((a.lo.add b.lo .down).val : ℚ) : ℝ) ≤ ((a.lo.val : ℚ) : ℝ) + ((b.lo.val : ℚ) : ℝ) := by
    exact_mod_cast val_add_down a.lo b.lo
  have u : ((a.hi.val : ℚ) : ℝ) + ((b.hi.val : ℚ) : ℝ) ≤ (((a.hi.add b.hi .up).val : ℚ) : ℝ) := by
    exact_mod_cast val_add_up a.hi b.hi
  exact ⟨d.trans (add_le_add a1 b1), (add_le_add a2 b2).trans u⟩

/-- The product of two bounds, where it is not marked bad, encloses the product. -/
theorem enclR_mul {a b : Bound} {x y : ℝ} (ha : EnclR a x) (hb : EnclR b y) :
    EnclR (a * b) (x * y) := fun h => by
  obtain ⟨g1, g2⟩ := inherit_good (r := ends (a.lo.mul b.lo .down) (a.hi.mul b.hi .up)) h
  obtain ⟨a1, a2⟩ := ha g1
  obtain ⟨b1, b2⟩ := hb g2
  have la : (0 : ℝ) ≤ ((a.lo.val : ℚ) : ℝ) := by exact_mod_cast val_nonneg a.lo
  have lb : (0 : ℝ) ≤ ((b.lo.val : ℚ) : ℝ) := by exact_mod_cast val_nonneg b.lo
  have ua : (0 : ℝ) ≤ ((a.hi.val : ℚ) : ℝ) := by exact_mod_cast val_nonneg a.hi
  have d : (((a.lo.mul b.lo .down).val : ℚ) : ℝ) ≤ ((a.lo.val : ℚ) : ℝ) * ((b.lo.val : ℚ) : ℝ) := by
    exact_mod_cast val_mul_down a.lo b.lo
  have u : ((a.hi.val : ℚ) : ℝ) * ((b.hi.val : ℚ) : ℝ) ≤ (((a.hi.mul b.hi .up).val : ℚ) : ℝ) := by
    exact_mod_cast val_mul_up a.hi b.hi
  exact ⟨d.trans (mul_le_mul a1 b1 lb (la.trans a1)),
    (mul_le_mul a2 b2 (lb.trans b1) ua).trans u⟩

/-- The power of a bound, where it is not marked bad, encloses the power. -/
theorem enclR_pow {a : Bound} {x : ℝ} (ha : EnclR a x) (n : ℕ) : EnclR (a.pow n) (x ^ n) :=
  fun h => by
  obtain ⟨g1, _⟩ := inherit_good (r := ends (a.lo.pow n .down) (a.hi.pow n .up)) h
  obtain ⟨a1, a2⟩ := ha g1
  have la : (0 : ℝ) ≤ ((a.lo.val : ℚ) : ℝ) := by exact_mod_cast val_nonneg a.lo
  have d : (((a.lo.pow n .down).val : ℚ) : ℝ) ≤ ((a.lo.val : ℚ) : ℝ) ^ n := by
    exact_mod_cast val_pow_down a.lo n
  have u : ((a.hi.val : ℚ) : ℝ) ^ n ≤ (((a.hi.pow n .up).val : ℚ) : ℝ) := by
    exact_mod_cast val_pow_up a.hi n
  exact ⟨d.trans (pow_le_pow_left₀ la a1 n), (pow_le_pow_left₀ (la.trans a1) a2 n).trans u⟩

/-- The difference of two bounds, where it is not marked bad, encloses the difference. -/
theorem enclR_sub {a b : Bound} {x y : ℝ} (ha : EnclR a x) (hb : EnclR b y) :
    EnclR (a - b) (x - y) := fun h => by
  have h' : (Bound.sub a b).bad = false := h
  show (((Bound.sub a b).lo.val : ℚ) : ℝ) ≤ x - y ∧ x - y ≤ (((Bound.sub a b).hi.val : ℚ) : ℝ)
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
    have hlo : b.lo.val ≤ a.hi.val := by
      have e1 : ((b.lo.val : ℚ) : ℝ) ≤ ((a.hi.val : ℚ) : ℝ) := by
        have e2 : ((b.hi.val : ℚ) : ℝ) < ((a.lo.val : ℚ) : ℝ) := by exact_mod_cast hlt
        linarith
      exact_mod_cast e1
    have d : (((a.lo.sub b.hi .down).val : ℚ) : ℝ) ≤
        ((a.lo.val : ℚ) : ℝ) - ((b.hi.val : ℚ) : ℝ) := by
      exact_mod_cast val_sub_down a.lo b.hi hlt.le
    have u : ((a.hi.val : ℚ) : ℝ) - ((b.lo.val : ℚ) : ℝ) ≤
        (((a.hi.sub b.lo .up).val : ℚ) : ℝ) := by
      exact_mod_cast val_sub_up a.hi b.lo hlo
    exact ⟨d.trans (by linarith), le_trans (by linarith) u⟩

/-- The quotient of two bounds, where it is not marked bad, encloses the quotient. -/
theorem enclR_div {a b : Bound} {x y : ℝ} (ha : EnclR a x) (hb : EnclR b y) :
    EnclR (a / b) (x / y) := fun h => by
  have h' : (Bound.div a b).bad = false := h
  show (((Bound.div a b).lo.val : ℚ) : ℝ) ≤ x / y ∧ x / y ≤ (((Bound.div a b).hi.val : ℚ) : ℝ)
  unfold Bound.div at h' ⊢
  split at h'
  · cases h'
  · rename_i hc
    rw [if_neg hc]
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hc
    obtain ⟨⟨g1, g2⟩, g3⟩ := hc
    obtain ⟨a1, a2⟩ := ha g1
    obtain ⟨b1, b2⟩ := hb g2
    have l0q : 0 < b.lo.val := val_pos _ g3
    have l0 : (0 : ℝ) < ((b.lo.val : ℚ) : ℝ) := by exact_mod_cast l0q
    have y0 : 0 < y := l0.trans_le b1
    have h0 : (0 : ℝ) < ((b.hi.val : ℚ) : ℝ) := y0.trans_le b2
    have la : (0 : ℝ) ≤ ((a.lo.val : ℚ) : ℝ) := by exact_mod_cast val_nonneg a.lo
    have ua : (0 : ℝ) ≤ ((a.hi.val : ℚ) : ℝ) := by exact_mod_cast val_nonneg a.hi
    have hlom : b.lo.m ≠ 0 := by simpa [isZero] using g3
    have hhim : b.hi.m ≠ 0 := by
      intro hz
      have e : b.hi.val = 0 := by simp [val, hz]
      rw [e] at h0
      simp at h0
    have d : (((a.lo.div b.hi .down).val : ℚ) : ℝ) ≤
        ((a.lo.val : ℚ) : ℝ) / ((b.hi.val : ℚ) : ℝ) := by
      exact_mod_cast val_div_down a.lo b.hi hhim
    have u : ((a.hi.val : ℚ) : ℝ) / ((b.lo.val : ℚ) : ℝ) ≤
        (((a.hi.div b.lo .up).val : ℚ) : ℝ) := by
      exact_mod_cast val_div_up a.hi b.lo hlom
    exact ⟨d.trans (div_le_div₀ (la.trans a1) a1 y0 b2), (div_le_div₀ ua a2 l0 b1).trans u⟩

/-- The upper end of a bound that is not bad, as `error` returns it, is at least what the bound
encloses. -/
theorem le_errorR {b : Bound} {x : ℝ} (hb : EnclR b x) (h : b.bad = false) :
    x ≤ ((b.error.val : ℚ) : ℝ) := by
  unfold error
  rw [h]
  exact (hb h).2

end Bound

end OnBytes.Params

#print axioms OnBytes.Params.isqrt_eq
#print axioms OnBytes.Params.Binary.val_sqrt_down
#print axioms OnBytes.Params.Binary.val_sqrt_up
#print axioms OnBytes.Params.Bound.enclR_sqrt
#print axioms OnBytes.Params.Bound.enclR_div
