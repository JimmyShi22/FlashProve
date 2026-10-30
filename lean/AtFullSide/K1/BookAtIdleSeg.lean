-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/BookAtIdleSeg.lean: the shared "sending" (the kind K1): ONE PASS: the test lendsOk accepts the carrying entries of the chain of segments. Cut out of BookAtIdle.lean, statements unturned, so
that Lean's kernel walks one long written list in one process (with both walks in one file a build under a cap of 32 GiB
died on another house's lane). Public data alone. No property of the protocol is claimed.
-/
import AtFullSide.K1.BookAtIdleWants

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K1
open VerifiableInference.Desc
open ProofFile.Honest
open AtFullSide.K14

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test accepts the carrying entries of the chain of segments. -/
theorem seg_lend : rawSegW.all lendsOk = true := by
  unfold rawSegW ProofFile.Honest.segmentCarries ProofFile.Honest.linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

end AtFullSide.K1

#print axioms AtFullSide.K1.seg_lend
