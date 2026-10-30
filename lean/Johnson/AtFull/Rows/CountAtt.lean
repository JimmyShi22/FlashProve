-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/CountAtt.lean: THE ATTENTION's WRITTEN ARM: ITS ROUNDS SEND 4190 SCALARS.
One closed fact by Lean's kernel, alone in its file. A law file; no running text imports it. Nothing
on codes.

  `count_att_walk`: the closed fact: the walk over the arm's pieces says yes (`countIsW`,
    Johnson/AtFull/Rows/CountPieces.lean).
  `count_att`: armCount (armAtW 1) = .ok 4190.
  `count_att_is`: ArmCount.lean's test with code says yes.
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
theorem count_att_walk : countIsW (armAtW 1) 4190 = true := by
  decide +kernel

theorem count_att : armCount (armAtW 1) = .ok 4190 := count_of_isW count_att_walk

theorem count_att_is : countIs (armAtW 1) 4190 = true := is_of_count count_att

end AtFull.Rows

#print axioms AtFull.Rows.count_att_walk
#print axioms AtFull.Rows.count_att
#print axioms AtFull.Rows.count_att_is
