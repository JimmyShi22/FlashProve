-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Head/HeadLinkRuns.lean: the head's link of the run on shapes: started from the written
value border337, members 337 to 352 return the written value border353LessPair.
How. Each of this link's four closed lines is turned into a fact RunsBetween, and the four are
chained, by the laws of Johnson/AtFull/Shape/Lines/JoinRecords.lean, with the layout file's size
from lay_size and, at member 347, headBatchingLight_standsUnder
(Johnson/AtFull/Shape/Lines/Head/HeadLight.lean).
What it is for. One of the 28 pieces (16 of the 358 members) that ShapeLines/FirstChainRuns.lean
joins, by the laws of Johnson/AtFull/Shape/Lines/JoinLinks.lean. The joined fact gives one premise
among several of the laws in Johnson/AtFull/Shape/RuleAtTable.lean. ShapeLines/README.md lists the
pieces.
Limits. That the run from startShA reaches border337 is not said here: that follows only when all
pieces before are chained from startShA and the last of them ends at this very value. RunsAll speaks
of every record that publicOfO returns at the stored full-size files and does not say that there is
one; record_there and RunsAll.ex (Johnson/AtFull/Shape/JoinAll.lean) give one under the layout
file's size. The run is the one over shapeL (LWn X₀), the text of the table over a record of
letters (Johnson/AtFull/Shape/TabLetters.lean); LWn X₀ checks nothing about X₀. yes_of_publicN
(Johnson/AtFull/Shape/YesAtZFullN.lean) takes a run that starts at member 0 to the table's own
steps, under further premises; for a piece that starts later no theorem states the like.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.JoinRecords
import Johnson.AtFull.Shape.Lines.Head.HeadLight
import AtFullSide.Layout.Size
import ShapeLines.Head.HeadLinkFirstPiece
import ShapeLines.Head.HeadLinkSecondPiece
import ShapeLines.Head.HeadLinkBatching
import ShapeLines.Head.HeadLinkLastPiece

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.PairAside

/-- At every record that publicOfO returns at the stored full-size files: from border337, the 16
members 337 to 352 of the run on shapes return border353LessPair. -/
theorem headLink_runs : RunsAll 337 16 border337 border353LessPair :=
  RunsBetween.runsAll
    ((((runsBetween_of_whole closingHint 337 3 (fun _ => border337) border340LessPair
        fun _ hX => atXLC_all Johnson.Unfolds.Layout.lay_size headLink_firstPiece hX).chain
      (runsBetween_of_lessPair closingHint 340 7 (fun _ => border340LessPair) border347LessPair
        fun _ hX => atXHC_all Johnson.Unfolds.Layout.lay_size headLink_secondPiece hX)).chain
      (runsBetween_of_step 347 (fun X => headBatchingLight (LWn X))
        (fun X _ _ h => headBatchingLight_standsUnder (LWn X) h)
        (borderWithPairOfRun closingHint 340 7 (fun _ => border340LessPair) border347LessPair)
        border348LessPair
        fun _ hX => atXHC_all Johnson.Unfolds.Layout.lay_size headLink_batching hX)).chain
      (runsBetween_of_whole closingHint 348 5
        (borderWithPairOfStep (fun X => headBatchingLight (LWn X))
          (borderWithPairOfRun closingHint 340 7 (fun _ => border340LessPair) border347LessPair)
          border348LessPair)
        border353LessPair
        fun _ hX => atXLC_all Johnson.Unfolds.Layout.lay_size headLink_lastPiece hX))

end ShapeLines

#print axioms ShapeLines.headLink_runs
