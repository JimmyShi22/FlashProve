-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/CountHead.lean: THE HEAD's WRITTEN ARM: ITS ROUNDS SEND 3570 SCALARS.
One closed fact by Lean's kernel, alone in its file. A law file; no running text imports it. Nothing
on codes.

  `count_head_walk`: the closed fact: the walk over the arm's pieces says yes (`countIsW`,
    Johnson/AtFull/Rows/CountPieces.lean).
  `count_head`: armCount (armAtW 24) = .ok 3570.
  `count_head_is`: ArmCount.lean's test with code says yes.
  Both follow from the closed fact; their statements are as they were.

Limits. A closed fact at a written arm (`armAtW`, Johnson/LPFE1R/RowsAtWritten.lean: an evaluator's
print): that a public part has this arm is shown nowhere here. The kernel runs the pieces of the
planner's routine of one link (`armPieces`), each piece from a plan without rounds; the heartbeats'
budget is lifted and the depth of recursion is set to 1000000. To run the
routine whole (`decide +kernel` on `countIs`) took 43 to 47.3 GiB resident. The cost, measured on
one machine, by `lean -j1` and by Lake, of this file and its three like: between half a minute and a
minute, mostly some 40 s; under 13 GiB resident. Nothing on soundness.

-/
import Johnson.AtFull.Rows.CountPieces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Rows
open VerifiableInference.Desc.LinkJoin

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem count_head_walk : countIsW (armAtW 24) 3570 = true := by
  decide +kernel

theorem count_head : armCount (armAtW 24) = .ok 3570 := count_of_isW count_head_walk

theorem count_head_is : countIs (armAtW 24) 3570 = true := is_of_count count_head

end AtFull.Rows

#print axioms AtFull.Rows.count_head_walk
#print axioms AtFull.Rows.count_head
#print axioms AtFull.Rows.count_head_is
