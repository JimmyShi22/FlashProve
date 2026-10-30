-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Head/HeadLinkLastPiece.lean: one closed line: the head's link, members 348 to 352 (by the
fields of Table.lean's rows: 348: behind; 349: equation; 350: close; 351: shut; 352: cleared).
How. The line's statement equates a closed Bool with true. Its proof term is Eq.refl true;
kernel_rfl leaves the comparison of the two sides to Lean's kernel.
Limits. Alone this line can be true although the step headBatchingLight, or the members before it,
returned an error: where the step did, look and lookHeard in this line's start are none. The line is
stated under atXLC although its start holds, as a term, the run of members 340 to 346 and the step
at member 347, and members of that run read the head's layout. No law says that members 348 to 352
leave that term unopened. Only with this link's three other lines, the laws of
Johnson/AtFull/Shape/Lines/JoinRecords.lean, headBatchingLight_standsUnder and the layout file's
size does it say that the link runs from border337. Nothing here says that the run from startShA
reaches border337. The run is written with runOverLightTail, over the cells of
Johnson/AtFull/Shape/Lines/TailLight.lean. At members 348 to 352 these are the cells of
shapeL (LWn X) themselves, but for member 350, where the step is closeGFH at the hint of link 24,
which is proved equal to the cell's step. The record is the one that atXLC gives to the test
(Johnson/AtFull/Shape/AtX.lean, Johnson/AtFull/Shape/AtXCounts.lean), not what publicOfO
returns. ShapeLines/Head/HeadLinkRuns.lean turns the line into a fact about what publicOfO returns,
by runFrom_eq_lightTail and atXLC_all.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.JoinRecords
import Johnson.Unfolds.KernelRfl
import ShapeLines.ClosingHint
import Johnson.AtFull.Shape.Lines.Head.HeadLight
import ShapeLines.Borders.Border340LessPair
import ShapeLines.Borders.Border347LessPair
import ShapeLines.Borders.Border348LessPair
import ShapeLines.Borders.Border353LessPair

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.PairAside

-- The comparison is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- From border348LessPair with the look and lookHeard that the step headBatchingLight left, members
348 to 352 return border353LessPair, all components compared. -/
theorem headLink_lastPiece :
    atXLC (fun X =>
      wholeB
        (runOverLightTail closingHint X 348 5
          (borderWithPairOfStep (fun X => headBatchingLight (LWn X))
            (borderWithPairOfRun closingHint 340 7 (fun _ => border340LessPair) border347LessPair)
            border348LessPair X))
        border353LessPair) = true := by
  kernel_rfl

end ShapeLines

#print axioms ShapeLines.headLink_lastPiece
