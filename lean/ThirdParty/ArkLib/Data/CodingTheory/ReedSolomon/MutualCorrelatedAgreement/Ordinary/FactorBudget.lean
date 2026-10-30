/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/FactorBudget.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 26 of the 44 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
* Proof changed, ordinaryUnifiedPowerFactorRawAt_sum_le: `beta_reduce` put before two
  `exact_mod_cast`: Lean 4.29.1 leaves (fun i ↦ ↑(height i)) i unreduced in the expected type.
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.Positivity
import ThirdParty.ArkLib.ToMathlib.BigOperators.LinearBudget

/-!
# Degree budgets for ordinary mutual correlated agreement

The ordinary mutual correlated agreement argument for Reed–Solomon codes factors an
interpolating polynomial into a content, which does not involve the root variable, and
irreducible factors of positive degree in the root variable. Each factor contributes a set of
exceptional challenges whose size is bounded in terms of the factor's height `h` (its degree in
the challenge variables) and its root degree. This file contains the arithmetic of those bounds.
It asserts nothing about polynomials; the geometric inputs are proved elsewhere.

In characteristic `p`, an irreducible factor of root degree `s * b` may be a Frobenius pullback
of a separable polynomial of root degree `b`, with `s` a power of `p`. The chart that
reconstructs the separable fiber has degree `ordinaryFrobeniusMixedDegree D h s b`, where `D` is
the message-degree bound. It is at most `h + s * b + 4 * D * h * (s * b)` (the inseparability
power costs nothing beyond the root degree `s * b`), at most
`h + s * b + (2 * D - 1) * h * (2 * (s * b) - 1)` when `b ≤ D`, and at most
`s * b + h * ordinaryPsi D (s * b)` without any hypothesis. The coefficient `ordinaryPsi D B`
equals the sharp coefficient `1 + (2 * D - 1) * (2 * B - 1)` for `B ≤ 2 * D + 1` and adds the
positive part `2 * (B - 2 * D - 1)` beyond that range.

The line, polynomial-curve and unified per-factor charges are bounded by a linear function of
height and root degree whose coefficients depend only on the total budgets. Since heights and root
degrees add up over the factorization, the content height plus all factor charges fits the charge
of the whole polynomial. This summation is
`Finset.add_sum_le_mul_add_mul_of_le`.

## Main statements

* `ReedSolomon.ordinaryFrobeniusMixedDegree_eq`, `ordinaryFrobeniusMixedDegree_le`,
  `ordinaryFrobeniusMixedDegree_le_sharp`, `ordinaryFrobeniusMixedDegree_le_unified`: the
  exact value of the mixed chart degree and its three upper bounds.
* `ReedSolomon.ordinaryFrobeniusCurveMixedDegree` is the chart degree for a Frobenius factor over
  a polynomial curve; `ordinaryFrobeniusCurveMixedDegree_eq` and
  `ordinaryFrobeniusCurveMixedDegree_le` give its exact form and a coarse upper bound.
* `ReedSolomon.ordinaryFrobenius_sharp_factor`, `ordinaryFrobenius_unified_factor`: the
  coefficient comparisons behind the sharp and unified bounds.
* `ReedSolomon.ordinaryPsi_eq_sharp`, `ordinaryPsi_mono`, `ordinaryPsi_le_four_mul`: the unified
  coefficient agrees with the sharp one up to `2 * D + 1`, is monotone, and is at most `4 * D * B`.
* `ReedSolomon.ordinaryFrobenius_charge_le`: a pullback factor is charged no more than a factor of
  root degree `s * b`.
* `ReedSolomon.ordinaryCurveFactorRaw` is the curve-factor charge;
  `ordinaryFrobeniusCurve_charge_le` and `ordinaryCurveFactorRaw_le_line_mul` compare these
  charges with the line charge.
* `ReedSolomon.ordinaryFactorRaw_le_linear`, `ordinaryCurveFactorRaw_le_linear`, and
  `ordinaryUnifiedPowerFactorRawAt_le_linear`: the linear bounds on per-factor charges;
  `ordinaryCurveFactorRaw_eq_linear` gives equality at the total budgets.
* `ReedSolomon.ordinaryFactorRaw_sum_le`, `ordinaryCurveFactorRaw_sum_le`,
  `ordinaryUnifiedPowerFactorRawAt_sum_le`, `ordinaryUnifiedPowerFactorRaw_sum_le`: content plus
  factor charges fit the total charge.
* `ReedSolomon.ordinaryUnifiedPowerFactorAt_succ_eq`: the free-retention budget at threshold
  `L = D + 1` is the fixed-split budget.
* `ReedSolomon.ordinaryFrobeniusCurveMixedDegree_le_unified` and
  `ordinaryFrobeniusCurve_charge_le_unifiedAt`: a Frobenius factor over a polynomial curve is
  charged no more than the free-retention charge at its original root degree.
* `ReedSolomon.ordinaryUnifiedPowerFactorRaw_le_ordinaryCurveFactorRaw`: the fixed-split charge
  is at most the curve-factor charge.

## References

* [DKT26]
-/

namespace ReedSolomon

open scoped BigOperators

/-! ### The mixed chart degree of a Frobenius factor -/

private theorem frobeniusMixedDegree_eq_aux (D h s b c : ℕ) :
    h * (1 + (2 * D * s - 1) * (b - 1)) + b * (c + (2 * D * s - 1) * h) =
      h + b * c + (2 * D * s - 1) * h * (2 * b - 1) := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hb
  simp only [Nat.add_sub_cancel_left, Nat.mul_add, Nat.mul_one]
  have ht : 2 + 2 * b - 1 = 1 + 2 * b := by omega
  rw [ht]
  ring

/-! ### Polynomial-curve mixed degree and charge -/

/-- The chart degree for a Frobenius factor over a degree-`ell` polynomial curve. Here `D` bounds
the message degree, `h` is the factor height, `s` is its Frobenius power, and `b` is the
separable root degree. -/
def ordinaryFrobeniusCurveMixedDegree (D ell h s b : ℕ) : ℕ :=
  h * (1 + (2 * D * s - 1) * (b - 1)) + b * (s * ell + (2 * D * s - 1) * h)

/-- The polynomial-curve chart degree is linear in the curve degree. -/
theorem ordinaryFrobeniusCurveMixedDegree_eq (D ell h s b : ℕ) :
    ordinaryFrobeniusCurveMixedDegree D ell h s b =
      h + ell * (s * b) + (2 * D * s - 1) * h * (2 * b - 1) := by
  change h * (1 + (2 * D * s - 1) * (b - 1)) +
      b * (s * ell + (2 * D * s - 1) * h) = _
  calc
    _ = h + b * (s * ell) + (2 * D * s - 1) * h * (2 * b - 1) :=
      frobeniusMixedDegree_eq_aux D h s b (s * ell)
    _ = h + ell * (s * b) + (2 * D * s - 1) * h * (2 * b - 1) := by ring

/-- The exceptional-set charge of a factor of root degree `a` and height `h` over a degree-`ell`
polynomial curve: `(2a - 1)h + theta * (h + ell*a + 4Dah) + ell*(n - D - 1)*a`. -/
def ordinaryCurveFactorRaw (theta : ℚ) (n D ell a h : ℕ) : ℚ :=
  ((2 * a - 1) * h : ℕ) +
    theta * (h + ell * a + 4 * D * a * h : ℕ) + (ell * ((n - D - 1) * a) : ℕ)

/-- The polynomial identity behind the sharp comparison:
`(2D - 1)(2sb - 1) - (2Ds - 1)(2b - 1) = 2(s - 1)(D - b)` in any commutative ring. -/
theorem ordinaryFrobenius_sharp_difference {R : Type*} [CommRing R] (D s b : R) :
    (2 * D - 1) * (2 * (s * b) - 1) - (2 * D * s - 1) * (2 * b - 1) =
      2 * (s - 1) * (D - b) := by
  ring

/-- When the separable degree satisfies `b ≤ D`, the coefficient `(2Ds - 1)(2b - 1)` is at most
the coefficient `(2D - 1)(2sb - 1)` of a separable factor of root degree `s * b`, in truncated
subtraction. The hypothesis `b ≤ D` is needed: for `D = 1` and `s = b = 2` the left side is `9`
and the right side is `7`. For `s = 0` or `b = 0` the left side is `0`. -/
theorem ordinaryFrobenius_sharp_factor {D s b : ℕ} (hD : b ≤ D) :
    (2 * D * s - 1) * (2 * b - 1) ≤ (2 * D - 1) * (2 * (s * b) - 1) := by
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp
  have hD1 : 1 ≤ D := hb.trans_le hD
  have hds : 1 ≤ 2 * D * s := by nlinarith [Nat.mul_le_mul hD1 hs]
  have hsb : 1 ≤ 2 * (s * b) := by nlinarith [Nat.mul_le_mul hs hb]
  have hD2 : 1 ≤ 2 * D := by omega
  have hb2 : 1 ≤ 2 * b := by omega
  zify [hds, hsb, hD2, hb2]
  have hsn : (0 : ℤ) ≤ (s : ℤ) - 1 := by omega
  have hDn : (0 : ℤ) ≤ (D : ℤ) - b := by omega
  nlinarith [mul_nonneg hsn hDn]

/-! ### The unified coefficient -/

/-- The coefficient of the challenge height in the ordinary joint-image degree bound, for root
degree `B` and message-degree bound `D`: the sharp coefficient `1 + (2D - 1)(2B - 1)` plus the
positive part `2 * (B - 2 * D - 1)`. Subtraction is truncated. -/
def ordinaryPsi (D B : ℕ) : ℕ :=
  1 + (2 * D - 1) * (2 * B - 1) + 2 * (B - 2 * D - 1)

/-- The unified coefficient is monotone in the root degree. -/
theorem ordinaryPsi_mono (D : ℕ) {B C : ℕ} (hBC : B ≤ C) :
    ordinaryPsi D B ≤ ordinaryPsi D C := by
  unfold ordinaryPsi
  apply Nat.add_le_add
  · exact Nat.add_le_add_left (Nat.mul_le_mul_left (2 * D - 1)
      (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hBC) 1)) 1
  · exact Nat.mul_le_mul_left 2
      (Nat.sub_le_sub_right (Nat.sub_le_sub_right hBC (2 * D)) 1)

/-- The unified coefficient is at most the coarse envelope `4 * D * B`. Both hypotheses are
needed, because `ordinaryPsi D B ≥ 1` always: `ordinaryPsi 0 1 = 1` and `ordinaryPsi 1 0 = 1`,
while the envelope is `0` in both cases. -/
theorem ordinaryPsi_le_four_mul {D B : ℕ} (hD : 1 ≤ D) (hB : 1 ≤ B) :
    ordinaryPsi D B ≤ 4 * D * B := by
  unfold ordinaryPsi
  have hDsub : 2 * D - 1 + 1 = 2 * D := Nat.sub_add_cancel (by omega)
  have hBsub : 2 * B - 1 + 1 = 2 * B := Nat.sub_add_cancel (by omega)
  by_cases hsmall : B ≤ 2 * D + 1
  · have hzero : B - 2 * D - 1 = 0 := by omega
    rw [hzero]
    nlinarith
  · have hlarge : 2 * D + 1 < B := Nat.lt_of_not_ge hsmall
    have hsub : B - 2 * D - 1 + (2 * D + 1) = B := by omega
    nlinarith

/-- The unified coefficient absorbs the coefficient `1 + (2Ds - 1)(2b - 1)` of every Frobenius
pullback, including the case `b > D` excluded from `ordinaryFrobenius_sharp_factor`. No
hypothesis is needed: if `s`, `b` or `D` is `0`, the left side is `1 ≤ ordinaryPsi D (s * b)`. -/
theorem ordinaryFrobenius_unified_factor (D s b : ℕ) :
    1 + (2 * D * s - 1) * (2 * b - 1) ≤ ordinaryPsi D (s * b) := by
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · simp [ordinaryPsi]
  rcases Nat.eq_zero_or_pos s with rfl | hs
  · simp [ordinaryPsi]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [ordinaryPsi]
  unfold ordinaryPsi
  by_cases hbD : b ≤ D
  · exact (Nat.add_le_add_left (ordinaryFrobenius_sharp_factor (s := s) hbD) 1).trans
      (Nat.le_add_right _ _)
  have hDb : D < b := Nat.lt_of_not_ge hbD
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hs) with hs1 | hsTwo
  · subst hs1
    simp
  have htailPos : 2 * D + 1 ≤ s * b := by nlinarith
  have hDs : 1 ≤ 2 * D * s := by nlinarith
  have hbTwo : 1 ≤ 2 * b := by omega
  have hDTwo : 1 ≤ 2 * D := by omega
  have hsbTwo : 1 ≤ 2 * (s * b) := by nlinarith
  have hsZ : (0 : ℤ) ≤ (s : ℤ) - 2 := by omega
  have hDZ : (0 : ℤ) ≤ D := by positivity
  have hbZ : (0 : ℤ) ≤ (b : ℤ) - D - 1 := by omega
  have htailZ :
      (2 : ℤ) * ((s : ℤ) - 1) * ((b : ℤ) - D) ≤
        2 * ((s : ℤ) * b - 2 * D - 1) := by
    nlinarith [mul_nonneg hDZ hsZ]
  have htailCast : ((s * b - 2 * D - 1 : ℕ) : ℤ) =
      (s : ℤ) * b - 2 * D - 1 := by omega
  zify [hDs, hbTwo, hDTwo, hsbTwo, htailPos]
  rw [htailCast] at *
  nlinarith [ordinaryFrobenius_sharp_difference (D : ℤ) (s : ℤ) (b : ℤ), htailZ]

/-! ### Per-factor charges with the coarse coefficient -/

/-- The exceptional-set charge of a factor of root degree `a ≥ 1` and height `h`, with the coarse
coefficient `1 + 4 * D * a`: `(2a - 1)h + theta * (h + a + 4Dah) + (n - D - 1)a`. Here `theta`
is the incidence ratio and `n` the block length. -/
def ordinaryFactorRaw (theta : ℚ) (n D a h : ℕ) : ℚ :=
  ((2 * a - 1) * h : ℕ) + theta * (h + a + 4 * D * a * h : ℕ) +
    ((n - D - 1) * a : ℕ)

/-! ### Per-factor charges with the unified coefficient -/

/-- The free-retention ordinary charge of a factor of root degree `B` and height `H`, for `ell`
interleaved rows, incidence ratio `theta`, block length `n`, and retention threshold `L`:
`(2B - 1)H + theta * (ell * B + H * ordinaryPsi D B) + ell * (n - L) * B`. The threshold `L`
enters the incidence ratio upstream and the accidental-agreement term `ell * (n - L) * B` here. -/
def ordinaryUnifiedPowerFactorRawAt
    (theta : ℚ) (n D ell B H L : ℕ) : ℚ :=
  ((2 * B - 1) * H : ℕ) + theta * (ell * B + H * ordinaryPsi D B : ℕ) +
    (ell * ((n - L) * B) : ℕ)

/-- The free-retention budget with incidence ratio `(n - L + 1) / (A - L + 1)`, where `A` is the
agreement threshold. -/
def ordinaryUnifiedPowerFactorAt (n D ell B H A L : ℕ) : ℚ :=
  ordinaryUnifiedPowerFactorRawAt
    (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) n D ell B H L

/-- The free-retention budget with the root-degree-zero case charged by the height alone. -/
def ordinaryUnifiedPowerFactorAtOrHeight (n D ell B H A L : ℕ) : ℚ :=
  if B = 0 then H else ordinaryUnifiedPowerFactorAt n D ell B H A L

/-- In root degree zero the budget is the height. -/
@[simp]
theorem ordinaryUnifiedPowerFactorAtOrHeight_zero (n D ell H A L : ℕ) :
    ordinaryUnifiedPowerFactorAtOrHeight n D ell 0 H A L = H := by
  simp [ordinaryUnifiedPowerFactorAtOrHeight]

/-- In positive root degree the budget is the free-retention budget. -/
theorem ordinaryUnifiedPowerFactorAtOrHeight_of_pos
    (n D ell B H A L : ℕ) (hB : 0 < B) :
    ordinaryUnifiedPowerFactorAtOrHeight n D ell B H A L =
      ordinaryUnifiedPowerFactorAt n D ell B H A L := by
  simp [ordinaryUnifiedPowerFactorAtOrHeight, Nat.ne_of_gt hB]

/-- At threshold `L = D + 1` the accidental-agreement term is `ell * ((n - D - 1) * B)`. -/
theorem ordinaryUnifiedPowerFactorRawAt_succ_eq
    (theta : ℚ) (n D ell B H : ℕ) :
    ordinaryUnifiedPowerFactorRawAt theta n D ell B H (D + 1) =
      ((2 * B - 1) * H : ℕ) + theta * (ell * B + H * ordinaryPsi D B : ℕ) +
        (ell * ((n - D - 1) * B) : ℕ) := by
  unfold ordinaryUnifiedPowerFactorRawAt
  have hn : n - (D + 1) = n - D - 1 := by omega
  rw [hn]

/-- The fixed-split ordinary charge, `ordinaryUnifiedPowerFactorRawAt` at threshold `D + 1`,
written with the accidental-agreement count `n - D - 1`. -/
def ordinaryUnifiedPowerFactorRaw (theta : ℚ) (n D ell B H : ℕ) : ℚ :=
  ((2 * B - 1) * H : ℕ) + theta * (ell * B + H * ordinaryPsi D B : ℕ) +
    (ell * ((n - D - 1) * B) : ℕ)

/-- The fixed-split charge is the free-retention charge at threshold `D + 1`. -/
theorem ordinaryUnifiedPowerFactorRaw_eq_rawAt (theta : ℚ) (n D ell B H : ℕ) :
    ordinaryUnifiedPowerFactorRaw theta n D ell B H =
      ordinaryUnifiedPowerFactorRawAt theta n D ell B H (D + 1) :=
  (ordinaryUnifiedPowerFactorRawAt_succ_eq theta n D ell B H).symm

/-- At threshold `L = D + 1` the free-retention budget is the fixed-split charge with incidence
ratio `(n - D) / (A - D)`. The hypotheses `D + 1 ≤ A` and `A ≤ n` are needed to rewrite
`n - (D + 1) + 1` and `A - (D + 1) + 1` as `n - D` and `A - D`. -/
theorem ordinaryUnifiedPowerFactorAt_succ_eq
    (n D ell B H A : ℕ) (hDA : D + 1 ≤ A) (hAn : A ≤ n) :
    ordinaryUnifiedPowerFactorAt n D ell B H A (D + 1) =
      ordinaryUnifiedPowerFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D ell B H := by
  have hn : n - (D + 1) + 1 = n - D := by omega
  have hA : A - (D + 1) + 1 = A - D := by omega
  unfold ordinaryUnifiedPowerFactorAt
  rw [hn, hA, ordinaryUnifiedPowerFactorRaw_eq_rawAt]

/-- For root degree `b ≤ B`, the free-retention charge is at most the linear function
`((2B - 1) + theta * ordinaryPsi D B) h + (theta * ell + ell * (n - L)) b`, whose coefficients
depend only on the total root-degree budget `B`. The hypothesis `0 ≤ theta` is needed to replace
`ordinaryPsi D b` by `ordinaryPsi D B`. -/
theorem ordinaryUnifiedPowerFactorRawAt_le_linear {theta : ℚ} (n D ell : ℕ) {b B : ℕ} (h L : ℕ)
    (htheta : 0 ≤ theta) (hb : b ≤ B) :
    ordinaryUnifiedPowerFactorRawAt theta n D ell b h L ≤
      ((2 * B - 1 : ℕ) + theta * ordinaryPsi D B) * h + (theta * ell + ell * (n - L : ℕ)) * b := by
  have hlinear : 2 * b - 1 ≤ 2 * B - 1 := Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hb) 1
  have hfirstQ : (((2 * b - 1) * h : ℕ) : ℚ) ≤ (2 * B - 1 : ℕ) * h := by
    exact_mod_cast Nat.mul_le_mul_right h hlinear
  have hpsiQ : ((h * ordinaryPsi D b : ℕ) : ℚ) ≤ h * ordinaryPsi D B := by
    exact_mod_cast Nat.mul_le_mul_left h (ordinaryPsi_mono D hb)
  unfold ordinaryUnifiedPowerFactorRawAt
  push_cast
  push_cast at hfirstQ hpsiQ
  nlinarith [mul_nonneg htheta (sub_nonneg.mpr hpsiQ)]

/-- At the total budgets, the free-retention charge equals the linear function of
`ordinaryUnifiedPowerFactorRawAt_le_linear`. -/
theorem ordinaryUnifiedPowerFactorRawAt_eq_linear (theta : ℚ) (n D ell B H L : ℕ) :
    ordinaryUnifiedPowerFactorRawAt theta n D ell B H L =
      ((2 * B - 1 : ℕ) + theta * ordinaryPsi D B) * H + (theta * ell + ell * (n - L : ℕ)) * B := by
  unfold ordinaryUnifiedPowerFactorRawAt
  push_cast
  ring

/-- The content height plus the free-retention charges of the factors indexed by `S` is at most
the free-retention charge of the whole polynomial, when root degrees add up to at most `B` and the
content and factor heights add up to at most `H`. The hypothesis `1 ≤ B` is needed: for `B = 0`,
`theta = 0`, `S = ∅` and content height `H = 1`, the left side is `1` and the right side `0`. -/
theorem ordinaryUnifiedPowerFactorRawAt_sum_le {I : Type*} (S : Finset I)
    (degree height : I → ℕ) (theta : ℚ) (n D ell B H L contentHeight : ℕ)
    (htheta : 0 ≤ theta) (hB : 1 ≤ B)
    (hdegree : ∑ i ∈ S, degree i ≤ B)
    (hheight : contentHeight + ∑ i ∈ S, height i ≤ H) :
    (contentHeight : ℚ) +
        ∑ i ∈ S, ordinaryUnifiedPowerFactorRawAt theta n D ell
          (degree i) (height i) L ≤
      ordinaryUnifiedPowerFactorRawAt theta n D ell B H L := by
  rw [ordinaryUnifiedPowerFactorRawAt_eq_linear]
  refine Finset.add_sum_le_mul_add_mul_of_le S (h := fun i ↦ (height i : ℚ))
    (a := fun i ↦ (degree i : ℚ)) (Nat.cast_nonneg _) ?_ (by positivity) ?_
    (by beta_reduce; exact_mod_cast hheight) (by beta_reduce; exact_mod_cast hdegree)
  · have hcast : (1 : ℚ) ≤ (2 * B - 1 : ℕ) := by exact_mod_cast (by omega : 1 ≤ 2 * B - 1)
    exact hcast.trans (le_add_of_nonneg_right (mul_nonneg htheta (by positivity)))
  · intro i hi
    exact ordinaryUnifiedPowerFactorRawAt_le_linear n D ell _ L htheta
      ((Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hi).trans hdegree)

/-! ### Curve factors with the unified coefficient -/

/-- The polynomial-curve mixed degree is at most `ell * (s * b) + h * ordinaryPsi D (s * b)`, with
no hypothesis on `D`, `ell`, `h`, `s` or `b`. -/
theorem ordinaryFrobeniusCurveMixedDegree_le_unified (D ell h s b : ℕ) :
    ordinaryFrobeniusCurveMixedDegree D ell h s b ≤
      ell * (s * b) + h * ordinaryPsi D (s * b) := by
  rw [ordinaryFrobeniusCurveMixedDegree_eq D ell h s b]
  have hcoefficient := ordinaryFrobenius_unified_factor D s b
  nlinarith

/-- A Frobenius pullback over a degree-`ell` polynomial curve, with separable degree `b` and power
`s`, is charged at most the free-retention charge of a factor of root degree `s * b` at every
retention threshold `L`. The hypothesis `1 ≤ s` is needed to compare `b` with `s * b`, and
`0 ≤ theta` to compare the incidence terms. -/
theorem ordinaryFrobeniusCurve_charge_le_unifiedAt (theta : ℚ) (n D ell h s b L : ℕ)
    (htheta : 0 ≤ theta) (hs : 1 ≤ s) :
    ((2 * b - 1) * h : ℕ) + theta * ordinaryFrobeniusCurveMixedDegree D ell h s b +
        (ell * ((n - L) * b) : ℕ) ≤
      ordinaryUnifiedPowerFactorRawAt theta n D ell (s * b) h L := by
  have hbs : b ≤ s * b := Nat.le_mul_of_pos_left b (by omega)
  have hmixed := ordinaryFrobeniusCurveMixedDegree_le_unified D ell h s b
  unfold ordinaryUnifiedPowerFactorRawAt
  apply add_le_add
  · apply add_le_add
    · exact_mod_cast Nat.mul_le_mul_right h
        (Nat.sub_le_sub_right (Nat.mul_le_mul_left 2 hbs) 1)
    · exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmixed) htheta
  · exact_mod_cast Nat.mul_le_mul_left ell (Nat.mul_le_mul_left (n - L) hbs)

/-- The fixed-split charge is at most the curve-factor charge `ordinaryCurveFactorRaw`, since
`ordinaryPsi D B ≤ 1 + 4 * D * B`. The hypothesis `1 ≤ D` is needed: `ordinaryPsi 0 2 = 3`. -/
theorem ordinaryUnifiedPowerFactorRaw_le_ordinaryCurveFactorRaw {theta : ℚ} (n : ℕ) {D : ℕ}
    (ell B H : ℕ) (htheta : 0 ≤ theta) (hD : 1 ≤ D) :
    ordinaryUnifiedPowerFactorRaw theta n D ell B H ≤ ordinaryCurveFactorRaw theta n D ell B H := by
  have hpsi : ordinaryPsi D B ≤ 1 + 4 * D * B := by
    rcases Nat.eq_zero_or_pos B with rfl | hB
    · simp [ordinaryPsi]
    · exact (ordinaryPsi_le_four_mul hD hB).trans (Nat.le_add_left _ _)
  have hmiddle : ell * B + H * ordinaryPsi D B ≤ H + ell * B + 4 * D * B * H := by
    have := Nat.mul_le_mul_left H hpsi
    nlinarith
  unfold ordinaryUnifiedPowerFactorRaw ordinaryCurveFactorRaw
  gcongr

end ReedSolomon
