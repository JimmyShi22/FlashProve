-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Link16Runs.lean: the layers' link 16 of the run on shapes: started from the
written value border225, members 225 to 238 return the written value border239.
How. layersLink_runs (Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean) at this link's
seventeen closed lines, with the layout file's size from lay_size. A second theorem says that there
is a record, by RunsAll.ex.
What it is for. A piece, 14 of the 358 members, for table_yes_of_runsAll (JoinTable.lean), which
pays one premise among several of RuleAtTable.lean's laws. README.md lists the pieces.
Limits. That the run from the first shape reaches border225 is not said here: that follows only when
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
import ShapeLines.Layers.Plan8Lines
import ShapeLines.Layers.Link16MembersOneToThree
import ShapeLines.Layers.Link16OwnRoundsGuards
import ShapeLines.Layers.Link16MergeRecords
import ShapeLines.Layers.Link16AfterOwnRounds
import ShapeLines.Layers.Link16MembersFiveToEight
import ShapeLines.Layers.Link16Batching
import ShapeLines.Layers.Link16MembersTenToFourteen

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- At every record that publicOfO returns at the stored full-size files: from border225, the
fourteen members 225 to 238 of the run on shapes return border239. -/
theorem layersLink16_runs : RunsAll 225 14 border225 border239 :=
  layersLink_runs Johnson.Unfolds.Layout.lay_size closingHint 16 (by decide) (by decide)
    layersBorders16 layersPlan8_lines
    layersLink16_membersOneToThree
    layersLink16_ownRoundsGuards
    layersLink16_mergeRecords
    layersLink16_afterOwnRounds
    layersLink16_membersFiveToEight
    layersLink16_batching
    layersLink16_membersTenToFourteen

/-- publicOfO returns a record at the stored full-size files, and there, from border225, the
fourteen members 225 to 238 of the run on shapes return border239. -/
theorem layersLink16_runs_at_a_record : ∃ X₀ : OnBytes.Model.Verify.Public,
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL
      (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
    (shapeL (LWn X₀)).runFrom 225 14 border225 = .ok border239 :=
  RunsAll.ex Johnson.Unfolds.Layout.lay_size layersLink16_runs

end ShapeLines

#print axioms ShapeLines.layersLink16_runs
#print axioms ShapeLines.layersLink16_runs_at_a_record
