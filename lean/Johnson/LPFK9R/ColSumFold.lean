-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK9R/ColSumFold.lean: `colSum` (TritsOfSums.lean: the sum of the matrices' columns, in the
letters of `k8TritsOf`: see there) IS `HTailF2.foldColumns` (OnBytes/Model/Tail.lean), at
every structure. One theorem: an identity of two folds over one array. No premise.

Why. Suppose it is shown, by the kernel, at the stored full-size example alone, that an attention
plan's `smallSize` is a written value whose field columns is 10248; columns is foldColumns. With
this identity that would pay the premise sA of `trits_of_sumA` (ColSumLayers.lean) AT THAT EXAMPLE's
PUBLIC PART. NOT in the goals' scope whole: there two exact numbers of the attention plan's shape
are still owed.
Limits. Nothing on any plan. No soundness statement.

-/
import Johnson.LPFK9R.TritsOfSums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFK9
open OnBytes OnBytes.Model

theorem colSum_fold (tl : HTailF2) : colSum tl = tl.foldColumns := by
  unfold colSum HTailF2.foldColumns
  rw [← Array.foldl_toList, List.foldl_map]

end LPFK9

#print axioms LPFK9.colSum_fold
