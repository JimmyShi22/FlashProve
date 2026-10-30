-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Link18Runs.lean: the layers' link 18 of the run on shapes: started from the
written value border253, members 253 to 266 return the written value border267.
How. layersLink_runs (Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean) at this link's
seventeen closed lines, with the layout file's size from lay_size. A second theorem says that there
is a record, by RunsAll.ex.
What it is for. A piece, 14 of the 358 members, for table_yes_of_runsAll (JoinTable.lean), which
pays one premise among several of RuleAtTable.lean's laws. README.md lists the pieces.
Limits. That the run from the first shape reaches border253 is not said here: that follows only when
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
import ShapeLines.Layers.Plan9Lines
import ShapeLines.Layers.Link18MembersOneToThree
import ShapeLines.Layers.Link18OwnRoundsGuards
import ShapeLines.Layers.Link18MergeRecords
import ShapeLines.Layers.Link18AfterOwnRounds
import ShapeLines.Layers.Link18MembersFiveToEight
import ShapeLines.Layers.Link18Batching
import ShapeLines.Layers.Link18MembersTenToFourteen

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- At every record that publicOfO returns at the stored full-size files: from border253, the
fourteen members 253 to 266 of the run on shapes return border267. -/
theorem layersLink18_runs : RunsAll 253 14 border253 border267 :=
  layersLink_runs Johnson.Unfolds.Layout.lay_size closingHint 18 (by decide) (by decide)
    layersBorders18 layersPlan9_lines
    layersLink18_membersOneToThree
    layersLink18_ownRoundsGuards
    layersLink18_mergeRecords
    layersLink18_afterOwnRounds
    layersLink18_membersFiveToEight
    layersLink18_batching
    layersLink18_membersTenToFourteen

/-- publicOfO returns a record at the stored full-size files, and there, from border253, the
fourteen members 253 to 266 of the run on shapes return border267. -/
theorem layersLink18_runs_at_a_record : ∃ X₀ : OnBytes.Model.Verify.Public,
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL
      (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
    (shapeL (LWn X₀)).runFrom 253 14 border253 = .ok border267 :=
  RunsAll.ex Johnson.Unfolds.Layout.lay_size layersLink18_runs

end ShapeLines

#print axioms ShapeLines.layersLink18_runs
#print axioms ShapeLines.layersLink18_runs_at_a_record
