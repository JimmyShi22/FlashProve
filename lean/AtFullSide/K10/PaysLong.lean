-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/PaysLong.lean: the closing of a segment (K10): the two long lists of the book name no closing in a way that
counts. Kernel evaluations at written values; the terms are the book's own.
-/
import AtFullSide.K14.RawEntriesKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open ProofFile.Honest AtFullSide.K14

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- No stretch of the book names a part at a place of the kind K10. -/
theorem wants_noClose : ((rawWantsW.map (·.entry)).all fun e => e.spender.place.kind != .K10) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- No carrying entry of the chain of segments spends, and none at a place of the kind K10 names a part but the first. -/
theorem seg_noClose : (rawSegW.all fun e => !e.once && (e.spender.place.kind != .K10 || e.spender.part == 0)) = true := by
  unfold rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel


end AtFullSide.K10

#print axioms AtFullSide.K10.wants_noClose
#print axioms AtFullSide.K10.seg_noClose
