-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Head/HeadLinkSecondPiece.lean: one closed line: the head's link, members 340 to 346 (by
the fields of Table.lean's rows: 340: lookCalls; 341: own; 342: reads; 343: draw; 344: digits; 345:
lookDigits; 346: merge).
How. The line's statement equates a closed Bool with true. Its proof term is Eq.refl true;
kernel_rfl leaves the comparison of the two sides to Lean's kernel.
Limits. The line starts from the written value border340LessPair; that members 337 to 339 return it
is the first piece's line. It is stated under atXHC. Members of it read the head's layout: member
340 through the letter look (lookOf, Johnson/AtFull/Shape/LettersAtX.lean; lookAt,
Johnson/Desc/First/Look/LookAt.lean), member 342 in its cell's text (TabL.readsHead,
Johnson/AtFull/Shape/TabLetters.lean). Under atXLC that layout is the unevaluated run of the
function that makes it, tests on the calls' tables included (xLazy, Johnson/AtFull/Shape/AtX.lean);
what was measured under either is in ShapeLines/README.md. Only with this link's three other lines,
the laws of Johnson/AtFull/Shape/Lines/JoinRecords.lean, headBatchingLight_standsUnder and the
layout file's size does it say that the link runs from border337. Nothing here says that the run
from startShA reaches border337. The run is written with runOverLightTail, over the cells of
Johnson/AtFull/Shape/Lines/TailLight.lean. At members 340 to 346 these are the cells of
shapeL (LWn X) themselves, but for member 340, where the step is callsGL, which is proved equal to
the cell's step. The record is the one that atXHC gives to the test (Johnson/AtFull/Shape/AtX.lean,
Johnson/AtFull/Shape/AtXCounts.lean), in which the head's layout is made without the tests on the
calls' tables; it is not what publicOfO returns. ShapeLines/Head/HeadLinkRuns.lean turns the
line into a fact about what publicOfO returns, by runFrom_eq_lightTail and atXHC_all.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.JoinRecords
import Johnson.Unfolds.KernelRfl
import ShapeLines.ClosingHint
import ShapeLines.Borders.Border340LessPair
import ShapeLines.Borders.Border347LessPair

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.PairAside

-- The comparison is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- From border340LessPair, members 340 to 346 return a shape which, with look and lookHeard set to
none, is border347LessPair. -/
theorem headLink_secondPiece :
    atXHC (fun X =>
      lessB (runOverLightTail closingHint X 340 7 border340LessPair) border347LessPair) = true := by
  kernel_rfl

end ShapeLines

#print axioms ShapeLines.headLink_secondPiece
