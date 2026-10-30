-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Attention/Link13Runs.lean: attention link 13 of the run on shapes: started from the
written value border183, members 183 to 196 return the written value border197.
How. four_all (Johnson/AtFull/Shape/JoinAll.lean) at this link's four closed lines, with the layout
file's size from lay_size.
What it is for. A piece, 14 of the 358 members, for table_yes_of_runsAll (JoinTable.lean), which
pays one premise among several of RuleAtTable.lean's laws. ShapeLines/README.md lists the pieces.
Limits. That the run from the first shape reaches border183 is not said here: that follows only when
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
import ShapeLines.Attention.Link13FirstPiece
import ShapeLines.Attention.Link13BatchingFront
import ShapeLines.Attention.Link13BatchingBack
import ShapeLines.Attention.Link13LastPiece

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.PairAside

/-- At every record that publicOfO returns at the stored full-size files: from border183, the
fourteen members 183 to 196 of the run on shapes return border197. -/
theorem attentionLink13_runs : RunsAll 183 14 border183 border197 :=
  four_all closingHint Johnson.Unfolds.Layout.lay_size 183 8 5 (l := 13) (by decide) (by decide)
    (by decide) 6 border183 border191LessPair border192LessPair border197
    claimsBehindSixthRowOfLink13
    shapeBehindSixthRowOfLink13LessPair.1
    attentionLink13_firstPiece attentionLink13_batchingFront attentionLink13_batchingBack
    attentionLink13_lastPiece

end ShapeLines

#print axioms ShapeLines.attentionLink13_runs
