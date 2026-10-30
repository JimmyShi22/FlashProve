-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Attention/Link5BatchingBack.lean: one closed line: attention link 5, the second part of
its batching (member 79): all after the sixth of its ten rows.
How. The statement equates a closed Bool with true. The proof term is Eq.refl true; kernel_rfl
leaves the comparison of the two sides to Lean's kernel.
Limits. Alone this line can be true although the batching's first part, or the members before it,
returned an error: where the first part did, look and lookHeard in this line's start are none. Only
with this link's three other lines, four_all and the layout file's size does it say that the link
runs from border71. Nothing here says that the run from the first shape reaches border71. The step
is one of the two parts into which JoinHalves.lean and BatchSplit.lean cut the batching's step on
shapes, not the step of shapeL (LWn X). The record is the one that atXLC hands in (AtX.lean,
AtXCounts.lean), not what publicOfO returns. four_all carries the line over, by half_join,
cellsH_eq and atXLC_zFull.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.JoinHalves
import Johnson.Unfolds.KernelRfl
import ShapeLines.ClosingHint
import ShapeLines.Borders.Border71
import ShapeLines.Borders.Border79LessPair
import ShapeLines.Borders.Border80LessPair
import ShapeLines.Borders.ClaimsBehindSixthRowOfLink5
import ShapeLines.Borders.ShapeBehindSixthRowOfLink5LessPair

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.PairAside

-- The comparison is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- From the written claims and chain's shape after the sixth row, with the look and lookHeard that
the first part left, the batching's second part returns a chain's shape. Paired with the second
component of border79LessPair, and with look and lookHeard set to none, it is border80LessPair.
(Premise P2b of four_all.) -/
theorem attentionLink5_batchingBack :
    atXLC (fun X =>
      backB
        (backH X 5 6
          (claimsBehindSixthRowOfLink5,
            withLkC shapeBehindSixthRowOfLink5LessPair.1
              (pairH (frontH X 5 6
                (withLk border79LessPair (lkA closingHint 71 8 border71 X))))))
        border79LessPair.2 border80LessPair) = true := by
  kernel_rfl

end ShapeLines

#print axioms ShapeLines.attentionLink5_batchingBack
