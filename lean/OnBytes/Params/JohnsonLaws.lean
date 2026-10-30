-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/JohnsonLaws.lean: what the planner's agreement, distance and count at an integer m
enclose; and radii in whole positions.

`johnson c m printed` (OnBytes/Params/Distance.lean) is a code at the distance that belongs to an
integer m. Its numbers are intervals made with the planner's square root. With
OnBytes/Params/SqrtLaws.lean this file says what they enclose, over the real numbers, each where it
is not marked bad. `Word.rho` is the rate k / n. `Word.agreeAt` is sqrt rho (1 + 1 / m), or sqrt rho
(1 + 1 / (2 m)) in the other reading of m, which is the printed reading of 2 m (`agreeAt_false`).
`countAt` is the formula of `johnsonCount` over the real numbers. The planner's agreement encloses
`agreeAt` (`enclR_johnson_agree`), its distance encloses 1 less that (`enclR_johnson_delta`), and
its count encloses `countAt` at the code's rate, that distance and m (`enclR_johnsonCount`,
`enclR_johnson_count`); where the count is not marked bad, 3 ≤ m and k < n (`johnson_count_good`).
For a rate above 0 the formula grows with the distance, from 0 on, and with m (`countAt_mono`).
Radii in whole positions, for any distance: `lowerRadius` and `upperRadius` are the lower and the
upper end of the distance times the length, rounded down. Where that product is not marked bad, the
lower radius is at most what the distance encloses, times the length (`lowerRadius_le`), and that
lies below the upper radius and one (`lt_upperRadius`); the product is not marked bad where the
distance is not and has its ends in order (`product_good`). Where the product is marked bad the
numbers mean nothing: a distance that failed gives the whole length. `johnsonRadius` is the lower
radius of the distance at m (`johnsonRadius_le`, `johnson_product_good`). Any e that is at most 1
less `agreeAt`, times the length, with m > 0 as printed, has e ≤ n and (m + 1) ^ 2 k n ≤ m ^ 2 (n -
e) ^ 2 (`radius_slack`), and so n k < (n - e) ^ 2 if k > 0 (`inJohnson_of_slack`,
`radius_inJohnson`): it is inside the Johnson radius, with the slack that belongs to m.

Main definitions: `Word.rho`, `Word.agreeAt`, `countAt`, `lowerRadius`, `upperRadius`,
`johnsonRadius`.
Main theorems: `enclR_rhoOf`, `enclR_johnson_agree`, `enclR_johnson_delta`, `enclR_johnsonCount`,
`enclR_johnson_count`, `johnson_count_good`, `countAt_mono`, `lowerRadius_le`, `lt_upperRadius`,
`product_good`, `johnsonRadius_le`, `johnson_product_good`, `agreeAt_false`, `radius_slack`,
`inJohnson_of_slack`, `radius_inJohnson`.
What is not claimed: that `countAt` bounds anything of a code: by the docstring of `johnsonCount` it
is the count of Theorem 4.6 of ePrint 2025/2055 with M = 1; that paper's text is not compared here,
and nothing of that theorem is proved in OnBytes/. Nothing on the planner's list size
(`johnsonList`). Nothing here on a code that is read at a distance which was not made from its own
m: where two codes are read at one distance, at most one of them is a `johnson c m printed`; for the
other see OnBytes/Params/AtDistanceJohnson.lean. Nothing here on a group's analysis
(OnBytes/Params/GroupJohnson.lean), or on which m the planner chooses. That a radius here is the
radius at which any round is priced: the planner prices by intervals. One radius with both limits:
the lower radius has the limit from above, the upper radius the limit from below; that the two are
the same number is no law; at a given code it can be tested. For proofs only; the program, that is
the Lean port built from OnBytes/, does not import this file.

-/
import OnBytes.Params.SqrtLaws
import OnBytes.Params.OrderedLaws
import OnBytes.Params.Distance

set_option autoImplicit false

namespace OnBytes.Params
open Bound

/-- The rate of a code as a real number: k / n. -/
noncomputable def Word.rho (c : Word) : ℝ := (c.k : ℝ) / (c.n : ℝ)

/-- The agreement that belongs to m: sqrt rho (1 + 1 / m) as the assumed theorem prints m, and
sqrt rho (1 + 1 / (2 m)) in the other reading. -/
noncomputable def Word.agreeAt (c : Word) (m : ℕ) (printed : Bool) : ℝ :=
  Real.sqrt c.rho + Real.sqrt c.rho / ((if printed then m else 2 * m : ℕ) : ℝ)

/-- The formula of `johnsonCount` over the real numbers, at a length, a rate, a distance and m. -/
noncomputable def countAt (n : ℕ) (rho delta : ℝ) (m : ℕ) : ℝ :=
  (2 * (((2 * m + 1 : ℕ) : ℝ) / 2) ^ 5 + 3 * (((2 * m + 1 : ℕ) : ℝ) / 2) * delta * rho) /
    (3 * rho * Real.sqrt rho) * (n : ℝ) + (((2 * m + 1 : ℕ) : ℝ) / 2) / Real.sqrt rho

/-- The planner's rate encloses the rate. -/
theorem enclR_rhoOf (c : Word) : EnclR (rhoOf c) c.rho := enclR_ratio c.k c.n

/-- **The planner's agreement at m encloses the agreement.** -/
theorem enclR_johnson_agree (c : Word) (m : ℕ) (printed : Bool) :
    EnclR (johnson c m printed).agree (c.agreeAt m printed) :=
  enclR_add (enclR_sqrt (enclR_rhoOf c)) (enclR_div (enclR_sqrt (enclR_rhoOf c)) (enclR_ofNat _))

/-- **The planner's distance at m encloses 1 less the agreement.** -/
theorem enclR_johnson_delta (c : Word) (m : ℕ) (printed : Bool) :
    EnclR (johnson c m printed).delta (1 - c.agreeAt m printed) := by
  have h := enclR_sub (enclR_ofWord 1) (enclR_johnson_agree c m printed)
  simpa using h

/-- The planner's formula for the count encloses the formula, at what its arguments enclose. -/
theorem enclR_johnsonCount (c : Word) {rho delta : Bound} {r d : ℝ} (hr : EnclR rho r)
    (hd : EnclR delta d) (m : ℕ) : EnclR (johnsonCount c rho delta m) (countAt c.n r d m) := by
  have hM : EnclR (Bound.ratio (2 * m + 1) 2) (((2 * m + 1 : ℕ) : ℝ) / 2) := by
    have h := enclR_ratio (2 * m + 1) 2
    simpa using h
  have h2 : EnclR (Bound.ofWord 2) (2 : ℝ) := by simpa using enclR_ofWord 2
  have h3 : EnclR (Bound.ofWord 3) (3 : ℝ) := by simpa using enclR_ofWord 3
  exact enclR_add
    (enclR_mul
      (enclR_div
        (enclR_add (enclR_mul h2 (enclR_pow hM 5)) (enclR_mul (enclR_mul (enclR_mul h3 hM) hd) hr))
        (enclR_mul (enclR_mul h3 hr) (enclR_sqrt hr)))
      (enclR_ofNat c.n))
    (enclR_div hM (enclR_sqrt hr))

/-- **The planner's count at m, where it is not marked bad, encloses `countAt`**, the formula of
`johnsonCount`, at the code's rate and at 1 less the agreement. -/
theorem enclR_johnson_count (c : Word) (m : ℕ) (printed : Bool) :
    EnclR (johnson c m printed).count (countAt c.n c.rho (1 - c.agreeAt m printed) m) := by
  intro g
  have e : (johnson c m printed).count =
      if (decide (m < 3) || decide (c.n ≤ c.k) ||
        (johnsonList (johnson c m printed).agree (rhoOf c)).2) = true then Bound.failed
      else johnsonCount c (rhoOf c) (johnson c m printed).delta m := rfl
  rw [e] at g ⊢
  split at g
  · cases g
  · rename_i hb
    rw [if_neg hb]
    exact enclR_johnsonCount c (enclR_rhoOf c) (enclR_johnson_delta c m printed) m g

/-- What a count that is not marked bad says of m and of the code. -/
theorem johnson_count_good {c : Word} {m : ℕ} {printed : Bool}
    (g : (johnson c m printed).count.bad = false) : 3 ≤ m ∧ c.k < c.n := by
  have e : (johnson c m printed).count =
      if (decide (m < 3) || decide (c.n ≤ c.k) ||
        (johnsonList (johnson c m printed).agree (rhoOf c)).2) = true then Bound.failed
      else johnsonCount c (rhoOf c) (johnson c m printed).delta m := rfl
  rw [e] at g
  split at g
  · cases g
  · rename_i hb
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, not_lt, not_le] at hb
    exact ⟨hb.1.1, hb.1.2⟩

/-- The formula grows with the distance, from 0 on, and with m. -/
theorem countAt_mono {n : ℕ} {rho d d' : ℝ} {m m' : ℕ} (hr : 0 < rho) (hd0 : 0 ≤ d) (hd : d ≤ d')
    (hm : m ≤ m') :
    countAt n rho d m ≤ countAt n rho d' m' := by
  unfold countAt
  have hs : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hr
  have hM : (((2 * m + 1 : ℕ) : ℝ) / 2) ≤ (((2 * m' + 1 : ℕ) : ℝ) / 2) := by
    have : ((2 * m + 1 : ℕ) : ℝ) ≤ ((2 * m' + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega)
    linarith
  have hM0 : (0 : ℝ) ≤ (((2 * m + 1 : ℕ) : ℝ) / 2) := by positivity
  have h5 := pow_le_pow_left₀ hM0 hM 5
  have hprod : 3 * (((2 * m + 1 : ℕ) : ℝ) / 2) * d * rho ≤
      3 * (((2 * m' + 1 : ℕ) : ℝ) / 2) * d' * rho := by
    have : (((2 * m + 1 : ℕ) : ℝ) / 2) * d ≤ (((2 * m' + 1 : ℕ) : ℝ) / 2) * d' :=
      mul_le_mul hM hd hd0 (hM0.trans hM)
    nlinarith
  have hden : 0 < 3 * rho * Real.sqrt rho := by positivity
  have h1 := div_le_div_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_left h5
    (by norm_num : (0 : ℝ) ≤ 2)) hprod) hden.le
  have h2 := mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ))
  have h3 := div_le_div_of_nonneg_right hM hs.le
  exact add_le_add h2 h3

/-- The lower end of a distance times a length, rounded down. It means nothing where that product is
marked bad: a distance that failed gives n. -/
def lowerRadius (delta : Bound) (n : ℕ) : ℕ := (delta * Bound.ofNat n).lo.floor

/-- The upper end of a distance times a length, rounded down. It means nothing where that product is
marked bad. Of the distance in `atDistance` it is that function's number of errors, by which it
tests for a third of the code's distance. -/
def upperRadius (delta : Bound) (n : ℕ) : ℕ := (delta * Bound.ofNat n).hi.floor

/-- **The lower radius is at most what the distance encloses, times the length.** -/
theorem lowerRadius_le {delta : Bound} {d : ℝ} {n : ℕ} (hd : EnclR delta d)
    (g : (delta * Bound.ofNat n).bad = false) : (lowerRadius delta n : ℝ) ≤ d * (n : ℝ) := by
  have h := (enclR_mul hd (enclR_ofNat n) g).1
  have f : ((lowerRadius delta n : ℚ) : ℝ) ≤ (((delta * Bound.ofNat n).lo.val : ℚ) : ℝ) := by
    exact_mod_cast Binary.floor_le _
  have f' : (lowerRadius delta n : ℝ) ≤ (((delta * Bound.ofNat n).lo.val : ℚ) : ℝ) := by
    simpa using f
  exact f'.trans h

/-- **What the distance encloses, times the length, lies below the upper radius and one.** -/
theorem lt_upperRadius {delta : Bound} {d : ℝ} {n : ℕ} (hd : EnclR delta d)
    (g : (delta * Bound.ofNat n).bad = false) : d * (n : ℝ) < (upperRadius delta n : ℝ) + 1 := by
  have h := (enclR_mul hd (enclR_ofNat n) g).2
  have f : (((delta * Bound.ofNat n).hi.val : ℚ) : ℝ) < ((upperRadius delta n : ℚ) : ℝ) + 1 := by
    exact_mod_cast Binary.lt_floor _
  have f' := lt_of_le_of_lt h f
  simpa using f'

/-- Where a distance whose ends are in order is not marked bad, the distance times a length is
not. -/
theorem product_good {delta : Bound} (ho : Ordered delta) (g : delta.bad = false) (n : ℕ) :
    (delta * Bound.ofNat n).bad = false :=
  good_mul (encl_hi ho) (encl_ofNat n) g rfl

/-- A radius in whole positions for the distance at m: the lower end of delta * n, rounded down. It
means nothing where that product is marked bad: a distance that failed gives n. -/
def johnsonRadius (c : Word) (m : ℕ) (printed : Bool) : ℕ :=
  lowerRadius (johnson c m printed).delta c.n

/-- **That radius, where the product is not marked bad, is at most 1 less the agreement, times the
length.** -/
theorem johnsonRadius_le {c : Word} {m : ℕ} {printed : Bool}
    (g : ((johnson c m printed).delta * Bound.ofNat c.n).bad = false) :
    (johnsonRadius c m printed : ℝ) ≤ (1 - c.agreeAt m printed) * (c.n : ℝ) :=
  lowerRadius_le (enclR_johnson_delta c m printed) g

/-- Where the distance at m is not marked bad, the distance times the length is not. -/
theorem johnson_product_good {c : Word} {m : ℕ} {printed : Bool}
    (g : (johnson c m printed).delta.bad = false) :
    ((johnson c m printed).delta * Bound.ofNat c.n).bad = false :=
  product_good (ordered_sub _ _) g c.n

/-- The other reading of m is the printed reading of 2 m. -/
theorem agreeAt_false (c : Word) (m : ℕ) : c.agreeAt m false = c.agreeAt (2 * m) true := by
  simp [Word.agreeAt]

/-- **A radius that is at most the distance at m > 0, as the assumed theorem prints m, is inside the
Johnson radius with the slack that belongs to m**, in whole numbers. -/
theorem radius_slack {c : Word} {m e : ℕ} (hm : 0 < m)
    (he : (e : ℝ) ≤ (1 - c.agreeAt m true) * (c.n : ℝ)) :
    e ≤ c.n ∧ (m + 1) * (m + 1) * c.k * c.n ≤ m * m * ((c.n - e) * (c.n - e)) := by
  have hn : (0 : ℝ) < (c.n : ℝ) := by
    have : 0 < c.n := by unfold Word.n; positivity
    exact_mod_cast this
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hrho : 0 ≤ c.rho := by unfold Word.rho; positivity
  set s := Real.sqrt c.rho with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s * s = c.rho := Real.mul_self_sqrt hrho
  have ha : c.agreeAt m true = s + s / (m : ℝ) := by
    unfold Word.agreeAt
    simp [hs]
  have ha0 : 0 ≤ c.agreeAt m true := by rw [ha]; positivity
  have hen : (e : ℝ) ≤ (c.n : ℝ) := by nlinarith
  have hen' : e ≤ c.n := by exact_mod_cast hen
  refine ⟨hen', ?_⟩
  have hge : (s + s / (m : ℝ)) * (c.n : ℝ) ≤ (c.n : ℝ) - (e : ℝ) := by rw [← ha]; linarith
  have hmul : (((m : ℝ) + 1) * s) * (c.n : ℝ) ≤ (m : ℝ) * ((c.n : ℝ) - (e : ℝ)) := by
    have e1 : ((m : ℝ) + 1) * s = (m : ℝ) * (s + s / (m : ℝ)) := by field_simp
    rw [e1, mul_assoc]
    exact mul_le_mul_of_nonneg_left hge hm'.le
  have hl0 : 0 ≤ (((m : ℝ) + 1) * s) * (c.n : ℝ) := by positivity
  have hsq := mul_self_le_mul_self hl0 hmul
  have hk : c.rho * (c.n : ℝ) = (c.k : ℝ) := by unfold Word.rho; field_simp
  have lhs : (((m : ℝ) + 1) * s * (c.n : ℝ)) * (((m : ℝ) + 1) * s * (c.n : ℝ)) =
      ((m : ℝ) + 1) * ((m : ℝ) + 1) * (c.k : ℝ) * (c.n : ℝ) := by
    calc _ = ((m : ℝ) + 1) * ((m : ℝ) + 1) * (s * s * (c.n : ℝ)) * (c.n : ℝ) := by ring
      _ = _ := by rw [hss, hk]
  rw [lhs] at hsq
  have cast : (((m + 1) * (m + 1) * c.k * c.n : ℕ) : ℝ) ≤
      ((m * m * ((c.n - e) * (c.n - e)) : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hen']
    nlinarith
  exact_mod_cast cast

/-- The slack in whole numbers, for k n > 0, puts the radius inside the Johnson radius. -/
theorem inJohnson_of_slack {n k m e : ℕ} (hkn : 0 < k * n)
    (h : (m + 1) * (m + 1) * k * n ≤ m * m * ((n - e) * (n - e))) :
    n * k < (n - e) * (n - e) := by
  by_contra hc
  have hc' : (n - e) * (n - e) ≤ n * k := Nat.le_of_not_lt hc
  have h1 : m * m * ((n - e) * (n - e)) ≤ m * m * (n * k) := Nat.mul_le_mul_left _ hc'
  have h2 : m * m * (n * k) < (m + 1) * (m + 1) * k * n := by nlinarith
  omega

/-- So such a radius is inside the Johnson radius: n k < (n - e) ^ 2, if the code has k > 0. -/
theorem radius_inJohnson {c : Word} {m e : ℕ} (hm : 0 < m) (hk : 0 < c.k)
    (he : (e : ℝ) ≤ (1 - c.agreeAt m true) * (c.n : ℝ)) :
    c.n * c.k < (c.n - e) * (c.n - e) := by
  obtain ⟨_, h⟩ := radius_slack hm he
  have hn : 0 < c.n := by unfold Word.n; positivity
  have hkn : 0 < c.k * c.n := Nat.mul_pos hk hn
  by_contra hc
  have hc' : (c.n - e) * (c.n - e) ≤ c.n * c.k := Nat.le_of_not_lt hc
  have h1 : m * m * ((c.n - e) * (c.n - e)) ≤ m * m * (c.n * c.k) := Nat.mul_le_mul_left _ hc'
  have h2 : m * m * (c.n * c.k) < (m + 1) * (m + 1) * c.k * c.n := by nlinarith
  omega

end OnBytes.Params

#print axioms OnBytes.Params.countAt_mono
#print axioms OnBytes.Params.lowerRadius_le
#print axioms OnBytes.Params.lt_upperRadius
#print axioms OnBytes.Params.product_good
#print axioms OnBytes.Params.johnsonRadius_le
#print axioms OnBytes.Params.johnson_product_good
#print axioms OnBytes.Params.agreeAt_false
#print axioms OnBytes.Params.radius_slack
#print axioms OnBytes.Params.inJohnson_of_slack
#print axioms OnBytes.Params.radius_inJohnson
#print axioms OnBytes.Params.enclR_johnson_agree
#print axioms OnBytes.Params.enclR_johnson_delta
#print axioms OnBytes.Params.enclR_johnson_count
#print axioms OnBytes.Params.johnson_count_good
