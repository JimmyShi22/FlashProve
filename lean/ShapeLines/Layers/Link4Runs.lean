-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Link4Runs.lean: the layers' link 4 of the run on shapes: started from the written
value border57, members 57 to 70 return the written value border71.
How. layersLink_runs (Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean) at this link's
seventeen closed lines, with the layout file's size from lay_size. A second theorem says that there
is a record, by RunsAll.ex.
What it is for. A piece, 14 of the 358 members, for table_yes_of_runsAll (JoinTable.lean), which
pays one premise among several of RuleAtTable.lean's laws. README.md lists the pieces.
Limits. That the run from the first shape reaches border57 is not said here: that follows only when
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
import ShapeLines.Layers.Plan2Lines
import ShapeLines.Layers.Link4MembersOneToThree
import ShapeLines.Layers.Link4OwnRoundsGuards
import ShapeLines.Layers.Link4MergeRecords
import ShapeLines.Layers.Link4AfterOwnRounds
import ShapeLines.Layers.Link4MembersFiveToEight
import ShapeLines.Layers.Link4Batching
import ShapeLines.Layers.Link4MembersTenToFourteen

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- At every record that publicOfO returns at the stored full-size files: from border57, the
fourteen members 57 to 70 of the run on shapes return border71. -/
theorem layersLink4_runs : RunsAll 57 14 border57 border71 :=
  layersLink_runs Johnson.Unfolds.Layout.lay_size closingHint 4 (by decide) (by decide)
    layersBorders4 layersPlan2_lines
    layersLink4_membersOneToThree
    layersLink4_ownRoundsGuards
    layersLink4_mergeRecords
    layersLink4_afterOwnRounds
    layersLink4_membersFiveToEight
    layersLink4_batching
    layersLink4_membersTenToFourteen

/-- publicOfO returns a record at the stored full-size files, and there, from border57, the fourteen
members 57 to 70 of the run on shapes return border71. -/
theorem layersLink4_runs_at_a_record : ∃ X₀ : OnBytes.Model.Verify.Public,
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL
      (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
    (shapeL (LWn X₀)).runFrom 57 14 border57 = .ok border71 :=
  RunsAll.ex Johnson.Unfolds.Layout.lay_size layersLink4_runs

end ShapeLines

#print axioms ShapeLines.layersLink4_runs
#print axioms ShapeLines.layersLink4_runs_at_a_record
