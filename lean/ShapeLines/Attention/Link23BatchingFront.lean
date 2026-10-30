-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Attention/Link23BatchingFront.lean: one closed line: attention link 23, the first part of
its batching (member 331): the draw, the guard and the first six of its ten rows.
How. The statement equates a closed Bool with true. The proof term is Eq.refl true; kernel_rfl
leaves the comparison of the two sides to Lean's kernel.
Limits. Alone this line can be true although members 323 to 330 returned an error: look and
lookHeard in its start are then none. Only with this link's three other lines, four_all and the
layout file's size does it say that the link runs from border323. Nothing here says that the run
from the first shape reaches border323. The step is one of the two parts into which JoinHalves.lean
and BatchSplit.lean cut the batching's step on shapes, not the step of shapeL (LWn X). The
record is the one that atXLC hands in (AtX.lean, AtXCounts.lean), not what publicOfO returns.
four_all carries the line over, by half_join, cellsH_eq and atXLC_zFull.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.JoinHalves
import Johnson.Unfolds.KernelRfl
import ShapeLines.ClosingHint
import ShapeLines.Borders.Border323
import ShapeLines.Borders.Border331LessPair
import ShapeLines.Borders.ClaimsBehindSixthRowOfLink23
import ShapeLines.Borders.ShapeBehindSixthRowOfLink23LessPair

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.PairAside

-- The comparison is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- From border331LessPair with the look and lookHeard that members 323 to 330 left, the batching's
first part returns the written claims and a chain's shape which, with look and lookHeard set to
none, is the written one. (Premise P2a of four_all.) -/
theorem attentionLink23_batchingFront :
    atXLC (fun X =>
      frontB
        (frontH X 23 6 (withLk border331LessPair (lkA closingHint 323 8 border323 X)))
        claimsBehindSixthRowOfLink23
        shapeBehindSixthRowOfLink23LessPair.1) = true := by
  kernel_rfl

end ShapeLines

#print axioms ShapeLines.attentionLink23_batchingFront
