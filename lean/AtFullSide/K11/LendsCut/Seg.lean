-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/LendsCut/Seg.lean: no carrying entry of the chain of segments is handed to the kind's place.
One closed fact by evaluation in Lean's kernel, behind the library's equations for String.splitOn and
toNat?.
-/
import AtFullSide.K11.LendsCut.Small

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open AtFullSide.K14 (rawSegW)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **No carrying entry of the chain of segments stands at the kind's place.** -/
theorem k11_seg : (rawSegW.all fun e => e.spender.place != IM.k11Place) = true := by
  unfold rawSegW ProofFile.Honest.segmentCarries ProofFile.Honest.linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

end AtFullSide.K11

#print axioms AtFullSide.K11.k11_seg
