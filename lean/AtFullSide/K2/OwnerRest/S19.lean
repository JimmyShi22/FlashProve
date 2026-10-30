-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/OwnerRest/S19.lean: at the link 19, at the chain of segments' piece, by Lean's kernel.
-/
import AtFullSide.K2.OwnerRest.L19

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open ProofFile.Honest ProofFile.Honest.K14
open AtFullSide.K14
open ProofFile.Honest.K2.Law (placesW)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- At the chain of segments. -/
theorem segW19 : ((placesW.filter fun p => p.link == 19).all fun p =>
    decide (ownerEntriesIn rawSegW p = restS19)) = true := by
  unfold rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

end AtFullSide.K2

#print axioms AtFullSide.K2.segW19
