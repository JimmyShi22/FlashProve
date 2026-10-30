-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Attention/Link3Runs.lean: attention link 3 of the run on shapes: started from the written
value border43, members 43 to 56 return the written value border57.
How. four_all (Johnson/AtFull/Shape/JoinAll.lean) at this link's four closed lines, with the layout
file's size from lay_size.
What it is for. A piece, 14 of the 358 members, for table_yes_of_runsAll (JoinTable.lean), which
pays one premise among several of RuleAtTable.lean's laws. ShapeLines/README.md lists the pieces.
Limits. That the run from the first shape reaches border43 is not said here: that follows only when
all pieces before are chained from startShA and the last of them ends at this very value. RunsAll
speaks of every record that publicOfO returns and does not say that there is one; record_there and
RunsAll.ex (JoinAll.lean) give one under the layout file's size. The run is the one over the table's
second text, shapeL (LWn X₀); LWn X₀ is no test on X₀; from there to the table's own steps it takes
yes_of_publicN, under the head. No second checker has replayed this link's lines. lay_size rests on
AtFullSide/Layout/TieRfl.lean, whose head reports that the program leanchecker fails at that module,
while a replay inside Lean passes at a thread stack of 128 MB.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.JoinAll
import AtFullSide.Layout.Size
import ShapeLines.Attention.Link3FirstPiece
import ShapeLines.Attention.Link3BatchingFront
import ShapeLines.Attention.Link3BatchingBack
import ShapeLines.Attention.Link3LastPiece

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.PairAside

/-- At every record that publicOfO returns at the stored full-size files: from border43, the
fourteen members 43 to 56 of the run on shapes return border57. -/
theorem attentionLink3_runs : RunsAll 43 14 border43 border57 :=
  four_all closingHint Johnson.Unfolds.Layout.lay_size 43 8 5 (l := 3) (by decide) (by decide)
    (by decide) 6 border43 border51LessPair border52LessPair border57
    claimsBehindSixthRowOfLink3
    shapeBehindSixthRowOfLink3LessPair.1
    attentionLink3_firstPiece attentionLink3_batchingFront attentionLink3_batchingBack
    attentionLink3_lastPiece

end ShapeLines

#print axioms ShapeLines.attentionLink3_runs
