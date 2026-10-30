-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/CountLayerFirst.lean: THE FIRST LAYERS' WRITTEN ARM: ITS ROUNDS SEND 4059
SCALARS. One closed fact by Lean's kernel, alone in its file. A law file; no running text imports
it. Nothing on codes.

  `count_layerFirst_walk`: the closed fact: the walk over the arm's pieces says yes (`countIsW`,
    Johnson/AtFull/Rows/CountPieces.lean).
  `count_layerFirst`: armCount (armAtW 0) = .ok 4059.
  `count_layerFirst_is`: ArmCount.lean's test with code says yes.
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
theorem count_layerFirst_walk : countIsW (armAtW 0) 4059 = true := by
  decide +kernel

theorem count_layerFirst : armCount (armAtW 0) = .ok 4059 := count_of_isW count_layerFirst_walk

theorem count_layerFirst_is : countIs (armAtW 0) 4059 = true := is_of_count count_layerFirst

end AtFull.Rows

#print axioms AtFull.Rows.count_layerFirst_walk
#print axioms AtFull.Rows.count_layerFirst
#print axioms AtFull.Rows.count_layerFirst_is
