-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Head/HeadLinkBatching.lean: one closed line: the head's link, member 347 (by the fields
of Table.lean's rows: 347: batch).
How. The line's statement equates a closed Bool with true. Its proof term is Eq.refl true;
kernel_rfl leaves the comparison of the two sides to Lean's kernel.
Limits. Alone this line can be true although members 340 to 346 returned an error: look and
lookHeard in its start are then none. Only with this link's three other lines, the laws of
Johnson/AtFull/Shape/Lines/JoinRecords.lean, headBatchingLight_standsUnder and the layout file's
size does it say that the link runs from border337. Nothing here says that the run from startShA
reaches border337. The step is headBatchingLight (Johnson/AtFull/Shape/Lines/Head/HeadLight.lean),
not the table's cell at member 347. Where headBatchingLight returns, that cell returns the same
(headBatchingLight_standsUnder); where it returns an error nothing is said of the cell. The record
is the one that atXHC gives to the test (Johnson/AtFull/Shape/AtX.lean,
Johnson/AtFull/Shape/AtXCounts.lean), in which the head's layout is made without the tests on the
calls' tables; it is not what publicOfO returns. ShapeLines/Head/HeadLinkRuns.lean turns the
line into a fact about what publicOfO returns, by runsBetween_of_step and atXHC_all.
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

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.PairAside

-- The comparison is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- From border347LessPair with the look and lookHeard that members 340 to 346 left, the step
headBatchingLight returns a shape which, with look and lookHeard set to none, is border348LessPair.
-/
theorem headLink_batching :
    atXHC (fun X =>
      lessB
        (headBatchingLight (LWn X)
          (borderWithPairOfRun closingHint 340 7 (fun _ => border340LessPair) border347LessPair X))
        border348LessPair) = true := by
  kernel_rfl

end ShapeLines

#print axioms ShapeLines.headLink_batching
