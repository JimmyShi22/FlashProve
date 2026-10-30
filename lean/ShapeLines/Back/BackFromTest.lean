-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Back/BackFromTest.lean: The last four members of the run on shapes (by the fields of
Table.lean's rows: 354: test; 355: batching; 356: sendW; 357: sealing): started from the written
value border354LessPair, they return the written value border358.
How. One closed line, and one_all (Johnson/AtFull/Shape/JoinAll.lean) at it, with the layout file's
size from lay_size. The line's statement equates a closed Bool with true. Its proof term is
Eq.refl true; kernel_rfl leaves the comparison of the two sides to Lean's kernel.
What it is for. One of the 28 pieces (4 of the 358 members) that ShapeLines/FirstChainRuns.lean
joins, by the laws of Johnson/AtFull/Shape/Lines/JoinLinks.lean. The joined fact gives one premise
among several of the laws in Johnson/AtFull/Shape/RuleAtTable.lean. ShapeLines/README.md lists the
pieces.
Limits. That the run from startShA reaches border354LessPair is not said here: that follows only
when all pieces before are chained from startShA and the last of them ends at this very value.
Limits of the line alone. The run is written with runH, over the cells of
Johnson/AtFull/Shape/TabLight.lean. At members 354 to 357 these are the cells of shapeL (LWn X)
themselves, and none of them reads the hint that runH takes. The record is the one that atXLC gives
to the test (Johnson/AtFull/Shape/AtX.lean, Johnson/AtFull/Shape/AtXCounts.lean), not what
publicOfO returns. one_all turns the line into a fact about what publicOfO returns, by cellsH_eq,
whose premise hpad_of_public pays at what publicOfO returns (Johnson/AtFull/Shape/TabLight.lean),
and atXLC_zFull.
Limits of the piece. RunsAll speaks of every record that publicOfO returns at the stored full-size
files and does not say that there is one; record_there and RunsAll.ex
(Johnson/AtFull/Shape/JoinAll.lean) give one under the layout file's size. The run is the one over
shapeL (LWn X₀), the text of the table over a record of letters
(Johnson/AtFull/Shape/TabLetters.lean); LWn X₀ checks nothing about X₀. yes_of_publicN
(Johnson/AtFull/Shape/YesAtZFullN.lean) takes a run that starts at member 0 to the table's own
steps, under further premises; for a piece that starts later no theorem states the like.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.JoinAll
import Johnson.Unfolds.KernelRfl
import AtFullSide.Layout.Size
import ShapeLines.ClosingHint
import ShapeLines.Borders.Border354LessPair
import ShapeLines.Borders.Border358

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.PairAside

-- The comparison is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- From border354LessPair, members 354 to 357 return border358, all components compared. -/
theorem backFromTest_line :
    atXLC (fun X =>
      wholeB (runH closingHint X 354 4 border354LessPair) border358) = true := by
  kernel_rfl

/-- At every record that publicOfO returns at the stored full-size files: from border354LessPair,
members 354 to 357 of the run on shapes return border358. -/
theorem backFromTest_runs : RunsAll 354 4 border354LessPair border358 :=
  one_all closingHint Johnson.Unfolds.Layout.lay_size 354 4
    border354LessPair border358 backFromTest_line

end ShapeLines

#print axioms ShapeLines.backFromTest_line
#print axioms ShapeLines.backFromTest_runs
