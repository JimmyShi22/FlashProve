/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/ToMathlib/BigOperators/LinearBudget.lean, commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13.
Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 1 of the 4 declarations of the file is kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Finite linear-budget arithmetic

Suppose each index `i` of a finite set carries a charge `x i` bounded by `c * h i + e * a i`,
where `h i` and `a i` are the index's shares of two budgets. If the shares of the first budget,
together with a separate nonnegative amount `r`, total at most `H`, and the shares of the second
budget total at most `B`, then `r` plus all charges is at most `c * H + e * B`, provided
`1 ≤ c` and `0 ≤ e`. The amount `r` is charged at rate one, so it costs no more than it would at
rate `c`.

Exceptional-set counts in mutual correlated agreement arguments are aggregated this way: every
irreducible factor of an interpolating polynomial contributes a count bounded linearly by its
height and root degree, the content contributes its height, and heights and root degrees add up
over the factorization.

For a finite set of columns with natural-number weights, `slotSurplusHeight` chooses a height from
the total weight and the difference between the number of columns and the row budget. The slot
sum at this height is strictly larger than the row budget times the number of coefficient slots
per row.

## Main statements

* `Finset.add_sum_le_mul_add_mul_of_le`: the aggregated bound in an ordered semiring.
* `Finset.sum_tsub_add_sum_eq_card_mul` and `Finset.slotSurplusHeight`: exact finite slot counts
  and their canonical height.
* `Finset.rows_mul_slotSurplusHeight_add_one_lt_sum_tsub`: the strict slot-surplus bound.
-/

namespace Finset

open scoped BigOperators

/-- If each charge satisfies `x i ≤ c * h i + e * a i`, the shares `h i` together with `r` total
at most `H`, and the shares `a i` total at most `B`, then `r + ∑ i ∈ s, x i ≤ c * H + e * B`.

The hypothesis `1 ≤ c` lets the amount `r`, charged at rate one, be absorbed at rate `c`; it also
gives `0 ≤ c`, which is needed to scale the first budget. The hypothesis `0 ≤ r` is needed as
well: with `s = ∅`, `r = H = -1`, `c = 2` and `e = B = 0` the conclusion reads `-1 ≤ -2`. The
hypothesis `0 ≤ e` is needed to scale the second budget. -/
theorem add_sum_le_mul_add_mul_of_le {ι R : Type*} [Semiring R] [PartialOrder R]
    [IsOrderedRing R] (s : Finset ι) {x h a : ι → R} {r c e H B : R}
    (hr : 0 ≤ r) (hc : 1 ≤ c) (he : 0 ≤ e)
    (hx : ∀ i ∈ s, x i ≤ c * h i + e * a i)
    (hH : r + ∑ i ∈ s, h i ≤ H) (hB : ∑ i ∈ s, a i ≤ B) :
    r + ∑ i ∈ s, x i ≤ c * H + e * B :=
  calc
    r + ∑ i ∈ s, x i ≤ c * r + ∑ i ∈ s, (c * h i + e * a i) :=
      add_le_add (le_mul_of_one_le_left hr hc) (sum_le_sum hx)
    _ = c * (r + ∑ i ∈ s, h i) + e * ∑ i ∈ s, a i := by
      rw [sum_add_distrib, mul_add, mul_sum, mul_sum, add_assoc]
    _ ≤ c * H + e * B :=
      add_le_add (mul_le_mul_of_nonneg_left hH (zero_le_one.trans hc))
        (mul_le_mul_of_nonneg_left hB he)

end Finset
