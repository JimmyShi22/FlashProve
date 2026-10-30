-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Link8Runs.lean: the layers' link 8 of the run on shapes: started from the written
value border113, members 113 to 126 return the written value border127.
How. layersLink_runs (Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean) at this link's
seventeen closed lines, with the layout file's size from lay_size. A second theorem says that there
is a record, by RunsAll.ex.
What it is for. A piece, 14 of the 358 members, for table_yes_of_runsAll (JoinTable.lean), which
pays one premise among several of RuleAtTable.lean's laws. README.md lists the pieces.
Limits. That the run from the first shape reaches border113 is not said here: that follows only when
all pieces before are chained from startShA and the last of them ends at this very value. RunsAll
speaks of every record that publicOfO returns and does not say that there is one; the second theorem
does. The run is the one over the table's second text, shapeL (LWn X₀); LWn X₀ is no test on X₀;
from there to the table's own steps it takes yes_of_publicN, under the head. No second checker has
replayed this link's lines. lay_size rests on AtFullSide/Layout/TieRfl.lean, whose head reports that
the program leanchecker fails at that module, while a replay inside Lean passes at a thread stack of
128 MB.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import AtFullSide.Layout.Size
import ShapeLines.Layers.Plan4Lines
import ShapeLines.Layers.Link8MembersOneToThree
import ShapeLines.Layers.Link8OwnRoundsGuards
import ShapeLines.Layers.Link8MergeRecords
import ShapeLines.Layers.Link8AfterOwnRounds
import ShapeLines.Layers.Link8MembersFiveToEight
import ShapeLines.Layers.Link8Batching
import ShapeLines.Layers.Link8MembersTenToFourteen

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- At every record that publicOfO returns at the stored full-size files: from border113, the
fourteen members 113 to 126 of the run on shapes return border127. -/
theorem layersLink8_runs : RunsAll 113 14 border113 border127 :=
  layersLink_runs Johnson.Unfolds.Layout.lay_size closingHint 8 (by decide) (by decide)
    layersBorders8 layersPlan4_lines
    layersLink8_membersOneToThree
    layersLink8_ownRoundsGuards
    layersLink8_mergeRecords
    layersLink8_afterOwnRounds
    layersLink8_membersFiveToEight
    layersLink8_batching
    layersLink8_membersTenToFourteen

/-- publicOfO returns a record at the stored full-size files, and there, from border113, the
fourteen members 113 to 126 of the run on shapes return border127. -/
theorem layersLink8_runs_at_a_record : ∃ X₀ : OnBytes.Model.Verify.Public,
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL
      (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
    (shapeL (LWn X₀)).runFrom 113 14 border113 = .ok border127 :=
  RunsAll.ex Johnson.Unfolds.Layout.lay_size layersLink8_runs

end ShapeLines

#print axioms ShapeLines.layersLink8_runs
#print axioms ShapeLines.layersLink8_runs_at_a_record
