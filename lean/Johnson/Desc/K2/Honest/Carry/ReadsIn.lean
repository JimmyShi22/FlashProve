-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Carry/ReadsIn.lean: WHAT THE CLAIM READS OF WHAT A FOLD LEFT, WITHIN ITS OWN
RANGES: `claimTrue_congr` (Johnson/Desc/K2/Honest/Carry/Left.lean) with its premise on the kept
members' tables asked at the indices below 2 ^ (the rows' bits + the code's length's logarithm)
alone: the range over which `ClaimTrue` (Johnson/Desc/K2/Honest/Inner/Statement.lean) sums. For what
a fold left that is kept in arrays of these sizes and is 0 beyond. One statement with its proof.

  `claimTrue_congr_in` two things that folds left, alike in the main row below the code's length, in
                    each kept member's table WITHIN THE CLAIM's OWN RANGE, and in the two mask rows
                    below the mask code's length, meet the claim together or not at all

By: the definitions. `claimTrue_congr` FOLLOWS FROM IT (its premise asks every index); both are
kept.

Limits. Neither claim is had here. Nothing on tails, pads or symbols. Nothing on any property.
-/
import Johnson.Desc.K2.Honest.Carry.Left

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE readE formAt)

/-- **What the claim reads of what a fold left, within its own ranges.** -/
theorem claimTrue_congr_in (Z : Sizes) (old : SingleRows) (W W' : Left)
    (h1 : ∀ j, j < (Z.codes.base.getD Z.code default).ell → W.main j = W'.main j)
    (h2 : ∀ a i, i < 2 ^ (ceilLog2 (Z.kept.getD a {}).mainRows +
        (Z.codes.base.getD Z.code default).logEll) →
      (W.kept a).entryIn (Z.kept.getD a {}) i = (W'.kept a).entryIn (Z.kept.getD a {}) i)
    (h3 : ∀ r i, r < 2 → i < (Z.codes.mask.getD Z.maskCode default).ell →
      W.mask r i = W'.mask r i) :
    ClaimTrue Z old W ↔ ClaimTrue Z old W' := by
  unfold ClaimTrue
  refine and_congr Iff.rfl (Eq.congr ?_ rfl)
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · exact Finset.sum_congr rfl fun j hj => by rw [h1 j (Finset.mem_range.1 hj)]
  · refine congrArg List.sum (List.map_congr_left fun f _ => ?_)
    cases (switchKept old).toList.idxOf? f.oracle with
    | none => rfl
    | some a => exact Finset.sum_congr rfl fun i hi => by rw [h2 a i (Finset.mem_range.1 hi)]
  · exact Finset.sum_congr rfl fun r hr => Finset.sum_congr rfl fun i hi => by
      rw [h3 r i (Finset.mem_range.1 hr) (Finset.mem_range.1 hi)]

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.claimTrue_congr_in
