-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Link2Runs.lean: the layers' link 2 of the run on shapes: started from the written
value border29, members 29 to 42 return the written value border43.
How. layersLink_runs (Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean) at this link's
seventeen closed lines, with the layout file's size from lay_size. A second theorem says that there
is a record, by RunsAll.ex.
What it is for. A piece, 14 of the 358 members, for table_yes_of_runsAll (JoinTable.lean), which
pays one premise among several of RuleAtTable.lean's laws. README.md lists the pieces.
Limits. That the run from the first shape reaches border29 is not said here: that follows only when
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
import ShapeLines.Layers.Plan1Lines
import ShapeLines.Layers.Link2MembersOneToThree
import ShapeLines.Layers.Link2OwnRoundsGuards
import ShapeLines.Layers.Link2MergeRecords
import ShapeLines.Layers.Link2AfterOwnRounds
import ShapeLines.Layers.Link2MembersFiveToEight
import ShapeLines.Layers.Link2Batching
import ShapeLines.Layers.Link2MembersTenToFourteen

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- At every record that publicOfO returns at the stored full-size files: from border29, the
fourteen members 29 to 42 of the run on shapes return border43. -/
theorem layersLink2_runs : RunsAll 29 14 border29 border43 :=
  layersLink_runs Johnson.Unfolds.Layout.lay_size closingHint 2 (by decide) (by decide)
    layersBorders2 layersPlan1_lines
    layersLink2_membersOneToThree
    layersLink2_ownRoundsGuards
    layersLink2_mergeRecords
    layersLink2_afterOwnRounds
    layersLink2_membersFiveToEight
    layersLink2_batching
    layersLink2_membersTenToFourteen

/-- publicOfO returns a record at the stored full-size files, and there, from border29, the fourteen
members 29 to 42 of the run on shapes return border43. -/
theorem layersLink2_runs_at_a_record : ∃ X₀ : OnBytes.Model.Verify.Public,
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL
      (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
    (shapeL (LWn X₀)).runFrom 29 14 border29 = .ok border43 :=
  RunsAll.ex Johnson.Unfolds.Layout.lay_size layersLink2_runs

end ShapeLines

#print axioms ShapeLines.layersLink2_runs
#print axioms ShapeLines.layersLink2_runs_at_a_record
