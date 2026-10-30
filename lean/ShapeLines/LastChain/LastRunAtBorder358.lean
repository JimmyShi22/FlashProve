-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/LastChain/LastRunAtBorder358.lean: one closed line: a run of guards on shapes over the
last chain's four members returns, started from the shape that doorShape
(AtFullSide/LaterThreads/DoorOnShapes.lean) makes of two ends.
The first end is handedOf border358 (AtFullSide/LaterThreads/FirstEndShape.lean). Six of its eight
components are read off border358, the written value at which the run on shapes over the first chain
ends. The other two are marks, on the statement and on the pending row's weights; handedOf sets both
to true, whatever the value is.
The second end is writtenSharedEnd (AtFullSide/LaterThreads/SharedEndShape.lean). It is a closed
term and is written out nowhere: what the last chain's start reads of the outcome of the guards' run
over the shared chain's twelve members, started from the shape of that chain's first state at a made
key.
The run is lastRunClosed (AtFullSide/LaterThreads/LastRunClosed.lean): the four guards of
writtenLastShape, at the typed sizes realSized and at piWFull, the written place of the request's
own proximity test.
How. The statement equates a closed Bool with true. The proof term is Eq.refl true; kernel_rfl
leaves the comparison of the two sides to Lean's kernel.
What it is for. last_end_accepts and taken_sources_accept
(AtFullSide/LaterThreads/LastRunClosed.lean) take lastRunClosed (doorShape a b) = true as a premise;
first_end_shape (AtFullSide/LaterThreads/FirstEndShape.lean) takes handedOf c = some a;
shared_end_at_the_head (AtFullSide/LaterThreads/SharedEndShape.lean) gives
writtenSharedEnd = some b. Cases on the two options in this line give the three equations at
c = border358.
What it shows besides. The statement's Bool is true only in the arm in which both ends are some
value. So the line shows, under no premise, that handedOf border358 is some value, that realSized is
some value and that the shared chain's run returns.
Limits. lastRunClosed alone is true where realSized is none; in this line it is reached only where
writtenSharedEnd is some value, and then realSized is some value too. The laws named above stand
under the premise HeadAtReturn; that writtenLastShape's guards are the guards at a description's own
letters is yes_is_written, under that premise. The two marks are not read off border358. Laws give
them: the mark on the weights, at the states reached at 358, is WeightsAtTheEnd, a premise of
first_end_shape, shown by weights_at_the_end under HeadAtReturn
(AtFullSide/LaterThreads/FirstEndShapeOfRun.lean); the mark on the statement is tidy_at_head's,
inside first_end_shape's proof. The shared end reaches an instance only where its key has the plan's
sizes (KeyHasTheSizes). The line says that the run returns and not what it returns: it ends at no
written value. On shapes alone: no member is shown to accept. That the run on shapes over the first
chain ends at border358 is runOnShapes_toEnd's (ShapeLines/FirstChainRuns.lean).
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import ShapeLines.Borders.Border358
import AtFullSide.LaterThreads.FirstEndShape
import AtFullSide.LaterThreads.LastRunClosed
import AtFullSide.LaterThreads.SharedEndShape
import Johnson.Unfolds.KernelRfl

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open AtFullSide.LaterThreads

-- The limit of heartbeats is lifted for the comparison.
set_option maxHeartbeats 0 in
/-- handedOf border358 and writtenSharedEnd are some values a and b, and from doorShape a b the run
of writtenLastShape's four guards returns. -/
theorem last_run_at_border358 :
    (match handedOf border358, writtenSharedEnd with
      | some a, some b => lastRunClosed (doorShape a b)
      | _, _ => false) = true := by
  kernel_rfl

end ShapeLines

#print axioms ShapeLines.last_run_at_border358
