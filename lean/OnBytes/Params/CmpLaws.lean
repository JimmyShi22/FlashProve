-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/CmpLaws.lean: the planner's comparison of two numbers is exact, and the sum, the
product and the power of bounds that enclose numbers are not marked bad.

OnBytes/Params/RealLaws.lean and OnBytes/Params/BoundLaws.lean prove that `le` and `lt` say yes only
of numbers in that order. This file proves the converse: `cmp` returns the order of the two values.
With it, the larger of two upper ends, as the planner picks it by `lt`, is at least both
(`larger_hi`, OnBytes/Slice/HeldKindsLink.lean [not in this library]; so here read: not proved in
this library). It also proves a part of what OnBytes/Params/BoundLaws.lean leaves open on the mark
`bad`: the sum, the product and the power of bounds that are not marked bad and enclose numbers are
not marked bad.

Main theorems, in the namespace `Binary`: `cmp_lt`, `cmp_eq`, `cmp_gt`, `le_of_not_lt`,
`lt_of_not_le`. In the namespace `Bound`: `good_add`, `good_mul`, `good_pow`.
What is not claimed: when a difference or a quotient is marked bad. `ratio` is a quotient, so
nothing is said on the mark of `fieldError`, `powersError`, `mcaError` or what is made of them.
Nothing on `sqrt`. Nothing on the C++ arithmetic, of which OnBytes/Params/Real.lean is a rendering.
For proofs only; the program, that is the Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.BoundLaws

set_option autoImplicit false

namespace OnBytes.Params
namespace Binary

/-- Where `cmp` returns `.lt`, the first value is below the second. -/
theorem cmp_lt (a b : Binary) (h : a.cmp b = .lt) : a.val < b.val :=
  lt_sound a b (by unfold lt; rw [h]; rfl)

/-- Where `cmp` returns `.gt`, the second value is below the first. -/
theorem cmp_gt (a b : Binary) (h : a.cmp b = .gt) : b.val < a.val := by
  unfold cmp at h
  split at h
  · rename_i hz
    split at h
    · split at h <;> cases h
    · rename_i ha
      have hb : b.isZero = true := by
        cases hb' : b.isZero
        · simp [hb'] at hz
          exact absurd hz ha
        · rfl
      rw [val_of_isZero b hb]
      exact val_pos a (by simpa using ha)
  · rename_i hz
    have ha : a.m ≠ 0 := by
      intro h0
      apply hz
      simp [isZero, h0]
    split at h
    · rename_i hne
      split at h
      · cases h
      · rename_i hnlt
        have hne' : a.top ≠ b.top := by simpa using hne
        have h1 : (2 : ℚ) ^ b.top ≤ (2 : ℚ) ^ (a.top - 1) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        exact ((val_lt_top b).trans_le h1).trans_le (top_le_val a ha)
    · split at h
      · rename_i he
        have hn : b.m < a.m * 2 ^ (a.e - b.e).toNat := Nat.compare_eq_gt.1 h
        show (b.m : ℚ) * 2 ^ b.e < (a.m : ℚ) * 2 ^ a.e
        rw [← val_lower a.m a.e b.e he]
        exact mul_lt_mul_of_pos_right (by exact_mod_cast hn) (two_zpow_pos _)
      · rename_i he
        have hn : b.m * 2 ^ (b.e - a.e).toNat < a.m := Nat.compare_eq_gt.1 h
        show (b.m : ℚ) * 2 ^ b.e < (a.m : ℚ) * 2 ^ a.e
        rw [← val_lower b.m b.e a.e (by omega)]
        exact mul_lt_mul_of_pos_right (by exact_mod_cast hn) (two_zpow_pos _)

/-- Where `cmp` returns `.eq`, the two values are equal. -/
theorem cmp_eq (a b : Binary) (h : a.cmp b = .eq) : a.val = b.val := by
  unfold cmp at h
  split at h
  · split at h
    · rename_i _ ha
      split at h
      · rename_i hb
        rw [val_of_isZero a ha, val_of_isZero b hb]
      · cases h
    · cases h
  · split at h
    · split at h <;> cases h
    · split at h
      · rename_i he
        have hn : a.m * 2 ^ (a.e - b.e).toNat = b.m := Nat.compare_eq_eq.1 h
        show (a.m : ℚ) * 2 ^ a.e = (b.m : ℚ) * 2 ^ b.e
        rw [← val_lower a.m a.e b.e he, hn]
      · rename_i he
        have hn : a.m = b.m * 2 ^ (b.e - a.e).toNat := Nat.compare_eq_eq.1 h
        show (a.m : ℚ) * 2 ^ a.e = (b.m : ℚ) * 2 ^ b.e
        rw [← val_lower b.m b.e a.e (by omega), ← hn]

/-- Where `lt` says no, the second value is at most the first. -/
theorem le_of_not_lt (a b : Binary) (h : a.lt b = false) : b.val ≤ a.val := by
  unfold lt at h
  cases hc : a.cmp b with
  | lt =>
    rw [hc] at h
    cases h
  | eq => exact (cmp_eq a b hc).ge
  | gt => exact (cmp_gt a b hc).le

/-- Where `le` says no, the second value is below the first. -/
theorem lt_of_not_le (a b : Binary) (h : a.le b = false) : b.val < a.val := by
  unfold le at h
  cases hc : a.cmp b with
  | gt => exact cmp_gt a b hc
  | lt =>
    rw [hc] at h
    cases h
  | eq =>
    rw [hc] at h
    cases h

end Binary

namespace Bound
open Binary

/-- Two ends in order are not marked. -/
theorem ends_good {l h : Binary} (hle : l.val ≤ h.val) : (ends l h).bad = false := by
  show h.lt l = false
  cases hc : h.lt l
  · rfl
  · exact absurd (lt_sound _ _ hc) (not_lt.2 hle)

/-- The sum of two bounds that are not marked bad and enclose numbers is not marked bad. -/
theorem good_add {a b : Bound} {x y : ℚ} (ha : Encl a x) (hb : Encl b y) (ga : a.bad = false)
    (gb : b.bad = false) : (a + b).bad = false := by
  obtain ⟨a1, a2⟩ := ha ga
  obtain ⟨b1, b2⟩ := hb gb
  show ((ends (a.lo.add b.lo .down) (a.hi.add b.hi .up)).bad || a.bad || b.bad) = false
  rw [ga, gb, ends_good (((val_add_down _ _).trans (add_le_add a1 b1)).trans
    ((add_le_add a2 b2).trans (val_add_up _ _)))]
  rfl

/-- The product of two bounds that are not marked bad and enclose numbers is not marked bad. -/
theorem good_mul {a b : Bound} {x y : ℚ} (ha : Encl a x) (hb : Encl b y) (ga : a.bad = false)
    (gb : b.bad = false) : (a * b).bad = false := by
  obtain ⟨a1, a2⟩ := ha ga
  obtain ⟨b1, b2⟩ := hb gb
  have x0 : 0 ≤ x := (val_nonneg _).trans a1
  have y0 : 0 ≤ y := (val_nonneg _).trans b1
  show ((ends (a.lo.mul b.lo .down) (a.hi.mul b.hi .up)).bad || a.bad || b.bad) = false
  rw [ga, gb, ends_good (((val_mul_down _ _).trans (mul_le_mul a1 b1 (val_nonneg _) x0)).trans
    ((mul_le_mul a2 b2 y0 (val_nonneg _)).trans (val_mul_up _ _)))]
  rfl

/-- The power of a bound that is not marked bad and encloses a number is not marked bad. -/
theorem good_pow {a : Bound} {x : ℚ} (ha : Encl a x) (ga : a.bad = false) (n : ℕ) :
    (a.pow n).bad = false := by
  obtain ⟨a1, a2⟩ := ha ga
  have x0 : 0 ≤ x := (val_nonneg _).trans a1
  show ((ends (a.lo.pow n .down) (a.hi.pow n .up)).bad || a.bad || a.bad) = false
  rw [ga, ends_good (((val_pow_down _ _).trans (pow_le_pow_left₀ (val_nonneg _) a1 n)).trans
    ((pow_le_pow_left₀ x0 a2 n).trans (val_pow_up _ _)))]
  rfl

end Bound
end OnBytes.Params

#print axioms OnBytes.Params.Binary.cmp_lt
#print axioms OnBytes.Params.Binary.cmp_gt
#print axioms OnBytes.Params.Binary.cmp_eq
#print axioms OnBytes.Params.Binary.le_of_not_lt
#print axioms OnBytes.Params.Binary.lt_of_not_le
#print axioms OnBytes.Params.Bound.ends_good
#print axioms OnBytes.Params.Bound.good_add
#print axioms OnBytes.Params.Bound.good_mul
#print axioms OnBytes.Params.Bound.good_pow
