-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/CBefore.lean: conjunct 11 of the tests on the plan at WK: beforeOk: every
oracle message that a block names as fixed before its first draw is sent, and where it is sampled
answered, in front of that draw. By an evaluation in Lean's kernel of the test's eager twin
(BeforeE.lean) at the written declared rounds. Negative tests: the first chain's declared rounds
without their first four (a gross bend: several causes); and one number moved: the batching's block
told 6 trees for 5 as sent in front of it.
Limits. At the closed description WK (WK.lean) and the written declared rounds alone. That a key
file's description passes the test at any public files is another file's, under named equations.
Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.WK
import Johnson.HB.LLHARD.KB4.BeforeE

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open Johnson.KB8 (declKeyFull)

set_option maxRecDepth 1000000 in
theorem before_full :
    beforeOkAt declKeyFull WK.first.blocksInOrder WK.shared.blocksInOrder WK.second.blocksInOrder = true := by
  decide +kernel

theorem WK_before : WK.beforeOk = true := by
  rw [beforeOk_at, WK_decl]
  exact before_full

set_option maxRecDepth 1000000 in
theorem before_bent :
    beforeOkAt (declKeyFull.1.drop 4, declKeyFull.2.1, declKeyFull.2.2) WK.first.blocksInOrder
      WK.shared.blocksInOrder WK.second.blocksInOrder = false := by
  decide +kernel

/-- The first chain where the batching of the rows on the table is told one tree more as sent in
front of it: made at declared rounds with one sending round more in front. So that block names the
message (1, 5), W's tree, which is sent behind its draw. -/
def firstSentMore : Chain FirstState Claim :=
  firstChainL (lookLinks lookE oneFull Lk6.AtPlan.keyFull.set) oneFull
    ({ entry := { name := "SEND", roots := 1 } } :: declKeyFull.1) toldKeyFull.1
    Johnson.KB8.rangesNumsFull

set_option maxRecDepth 1000000 in
/-- One number moved: the trees sent in front of the batching: 6 for 5. -/
theorem before_sent_bent :
    beforeOkAt declKeyFull firstSentMore.blocksInOrder WK.shared.blocksInOrder WK.second.blocksInOrder = false := by
  decide +kernel

end Johnson.KB4

#print axioms Johnson.KB4.before_full
#print axioms Johnson.KB4.WK_before
#print axioms Johnson.KB4.before_bent
#print axioms Johnson.KB4.before_sent_bent
