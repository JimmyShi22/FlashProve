/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/ToMathlib/Combinatorics/Enumerative/IncidenceProduct.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 7 of the 25 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Positivity

/-!
# Products of incidence ratios

Agreement incidence bounds count the points of a variety that agree with received data in at
least `A` of `n` positions. Each cut of a component of dimension `d` by one of the `n` position
equations costs a factor `((n - T + 1) * b) / (A - T + 1)`, where `b` bounds the degree of the
equations and a component of that dimension lies in fewer than `T` of the equations.
The bound for a component of dimension `d` is the product of these factors over the dimensions
`1, ..., d`.

This file defines these products and proves their elementary properties.

* `incidenceProduct n A b T d` is the product of the factors with threshold `T t` at dimension
  `t + 1`, for `t < d`.
* `dimensionSensitiveIncidenceProduct n A k b d` uses, at dimension `t + 1`, the factor
  `((n - k + t + 1) * b) / (A - k + t + 1)`. For `t < k ≤ A ≤ n` this is the factor with
  threshold `T = k - t`: a positive-dimensional component of dimension `t + 1` in the space of
  polynomials of degree less than `k` lies in at most `k - (t + 1)` evaluation equations at
  distinct points.
* `hybridDimensionSensitiveIncidenceProduct n A L k b d` uses the threshold `L` in dimension one
  and the threshold `k + 1 - t` in dimension `t + 1` for `t ≥ 1`.

Every factor is at least one when `A ≤ n` and `0 < b`, whatever the threshold, so under these
hypotheses the products are monotone in the dimension. The ratio `(n - m) / (A - m)` increases
with `m` for `m < A ≤ n`, which is how the number of identically vanishing equations is compared
with a threshold.

## Main statements

* `natCast_sub_div_natCast_sub_le`: `(n - m) / (A - m) ≤ (n - m') / (A - m')` for
  `m ≤ m' < A ≤ n`.
* `one_le_incidenceFactor`: each factor is at least one when `A ≤ n` and `0 < b`.
* `natCast_sub_mul_le_incidenceFactor_mul`: for `j < T ≤ A ≤ n`, the factor with threshold `T`
  bounds `(n - j) * b / (A - j)`, which makes it an admissible ratio in an incidence induction.
* `incidenceProduct_const`, `incidenceProduct_mono_dimension`: the product with a constant
  threshold is a power, and the product is monotone in the dimension when `A ≤ n` and `0 < b`.
* `dimensionSensitiveIncidenceProduct_eq_incidenceProduct`,
  `hybridDimensionSensitiveIncidenceProduct_eq_incidenceProduct`: the two named products as
  products with a threshold function.
* `dimensionSensitiveIncidenceProduct_eq_pow_mul`: the degree bound `b` contributes `b ^ d`.
* `dimensionSensitiveIncidenceProduct_le_one`: the products in dimension at most one are bounded
  by the first factor.
* `natCast_shiftedRatio_le_one_div` and
  `dimensionSensitiveIncidenceProduct_le_one_div_pow_of_gap`: shifted ratios and their products
  are bounded by powers of `1 / δ` under a linear gap condition.
* `natCastRatio_le_div_of_scaled_lower_bound`: a denominator lower bound gives a ratio bound.
* `dimensionSensitiveIncidenceProduct_mono_dimension` and
  `dimensionSensitiveIncidenceProduct_le_first_pow`: monotonicity and a fixed-threshold power
  bound.
* `hybridDimensionSensitiveIncidenceProduct_mono_dimension`,
  `hybridDimensionSensitiveIncidenceProduct_eq_factor_mul`,
  `hybridDimensionSensitiveIncidenceProduct_min_le`,
  `hybridDimensionSensitiveIncidenceProduct_le_two`: monotonicity, a factorization below the
  coefficient dimension, and upper bounds by initial factors.

## References

* [DKT26]
-/

/-- The incidence factor `((n - T + 1) * b) / (A - T + 1)` is at least one when `A ≤ n` and
`0 < b`, for every threshold `T`. -/
theorem one_le_incidenceFactor {n A T b : ℕ} (hAn : A ≤ n) (hb : 0 < b) :
    (1 : ℚ) ≤ ((((n - T + 1) * b : ℕ) : ℚ) / ((A - T + 1 : ℕ) : ℚ)) := by
  rw [one_le_div₀ (by exact_mod_cast (show 0 < A - T + 1 by omega))]
  exact_mod_cast (show A - T + 1 ≤ (n - T + 1) * b from
    (by omega : A - T + 1 ≤ n - T + 1).trans (Nat.le_mul_of_pos_right _ hb))

/-- For `j < T ≤ A ≤ n`, `(n - j) * (A - T + 1) ≤ (n - T + 1) * (A - j)`: removing `j` of `n`
elements and `j` of `A` elements gives a ratio at most the ratio for `T - 1` removed. -/
private theorem sub_mul_sub_add_one_le {n A T j : ℕ} (hj : j < T) (hTA : T ≤ A)
    (hAn : A ≤ n) :
    (n - j) * (A - T + 1) ≤ (n - T + 1) * (A - j) := by
  obtain ⟨z, rfl⟩ : ∃ z, T = j + 1 + z := ⟨T - j - 1, by omega⟩
  rw [show n - j = (n - (j + 1 + z) + 1) + z by omega,
    show A - j = (A - (j + 1 + z) + 1) + z by omega]
  have : A - (j + 1 + z) + 1 ≤ n - (j + 1 + z) + 1 := by omega
  nlinarith

/-- For `j < T ≤ A ≤ n`, the incidence factor `((n - T + 1) * b) / (A - T + 1)` is an admissible
ratio at `j`: `(n - j) * b ≤ ((n - T + 1) * b) / (A - T + 1) * (A - j)`. -/
theorem natCast_sub_mul_le_incidenceFactor_mul {n A T b j : ℕ} (hj : j < T) (hTA : T ≤ A)
    (hAn : A ≤ n) :
    (((n - j) * b : ℕ) : ℚ) ≤
      ((((n - T + 1) * b : ℕ) : ℚ) / ((A - T + 1 : ℕ) : ℚ)) * ((A - j : ℕ) : ℚ) := by
  have hc : (0 : ℚ) < ((A - T + 1 : ℕ) : ℚ) := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hc, ← Nat.cast_mul, ← Nat.cast_mul]
  have := Nat.mul_le_mul_right b (sub_mul_sub_add_one_le hj hTA hAn)
  exact_mod_cast (by nlinarith : (n - j) * b * (A - T + 1) ≤ (n - T + 1) * b * (A - j))

/-- The product over `t < d` of the incidence factors `((n - T t + 1) * b) / (A - T t + 1)` with
threshold `T t` at dimension `t + 1`. -/
def incidenceProduct (n A b : ℕ) (T : ℕ → ℕ) (d : ℕ) : ℚ :=
  ∏ t ∈ Finset.range d, ((((n - T t + 1) * b : ℕ) : ℚ) / ((A - T t + 1 : ℕ) : ℚ))

/-- The product of incidence factors is nonnegative. -/
theorem incidenceProduct_nonneg (n A b : ℕ) (T : ℕ → ℕ) (d : ℕ) :
    0 ≤ incidenceProduct n A b T d :=
  Finset.prod_nonneg fun _ _ ↦ div_nonneg (by positivity) (by positivity)

/-- With the constant threshold `L`, the product up to dimension `d` is the `d`-th power of the
factor `((n - L + 1) * b) / (A - L + 1)`. -/
theorem incidenceProduct_const (n A b L d : ℕ) :
    incidenceProduct n A b (fun _ ↦ L) d =
      ((((n - L + 1) * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^ d := by
  rw [incidenceProduct, Finset.prod_const, Finset.card_range]

/-- If `A ≤ n` and `0 < b`, every factor is at least one, so the product is monotone in the
dimension. -/
theorem incidenceProduct_mono_dimension {n A b : ℕ} (T : ℕ → ℕ) (hAn : A ≤ n)
    (hb : 0 < b) :
    Monotone (incidenceProduct n A b T) :=
  monotone_nat_of_le_succ fun d ↦ by
    simpa only [incidenceProduct, Finset.prod_range_succ] using
      (le_mul_of_one_le_right (incidenceProduct_nonneg n A b T d)
        (one_le_incidenceFactor hAn hb))
