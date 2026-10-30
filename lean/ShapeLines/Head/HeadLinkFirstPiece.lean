-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Head/HeadLinkFirstPiece.lean: one closed line: the head's link, members 337 to 339 (by
the fields of Table.lean's rows: 337: laid; 338: reply; 339: switch).
How. The line's statement equates a closed Bool with true. Its proof term is Eq.refl true;
kernel_rfl leaves the comparison of the two sides to Lean's kernel.
Limits. In builds of this file the kernel answered "deep recursion detected" at a thread stack of
128 MiB and accepted the line at 256 MiB (ShapeLines/README.md). Only with this link's three other
lines, the laws of Johnson/AtFull/Shape/Lines/JoinRecords.lean, headBatchingLight_standsUnder and
the layout file's size does it say that the link runs from border337. Nothing here says that the run
from startShA reaches border337. The run is written with runOverLightTail, over the cells of
Johnson/AtFull/Shape/Lines/TailLight.lean. At members 337 to 339 these are the cells of
shapeL (LWn X) themselves. The record is the one that atXLC gives to the test
(Johnson/AtFull/Shape/AtX.lean, Johnson/AtFull/Shape/AtXCounts.lean), not what publicOfO
returns. ShapeLines/Head/HeadLinkRuns.lean turns the line into a fact about what publicOfO returns,
by runFrom_eq_lightTail and atXLC_all.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.JoinRecords
import Johnson.Unfolds.KernelRfl
import ShapeLines.ClosingHint
import ShapeLines.Borders.Border337
import ShapeLines.Borders.Border340LessPair

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.PairAside

-- The comparison is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- From border337, members 337 to 339 return border340LessPair, all components compared. -/
theorem headLink_firstPiece :
    atXLC (fun X =>
      wholeB (runOverLightTail closingHint X 337 3 border337) border340LessPair) = true := by
  kernel_rfl

end ShapeLines

#print axioms ShapeLines.headLink_firstPiece
