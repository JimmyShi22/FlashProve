-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Link12Runs.lean: the layers' link 12 of the run on shapes: started from the
written value border169, members 169 to 182 return the written value border183.
How. layersLink_runs (Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean) at this link's
seventeen closed lines, with the layout file's size from lay_size. A second theorem says that there
is a record, by RunsAll.ex.
What it is for. A piece, 14 of the 358 members, for table_yes_of_runsAll (JoinTable.lean), which
pays one premise among several of RuleAtTable.lean's laws. README.md lists the pieces.
Limits. That the run from the first shape reaches border169 is not said here: that follows only when
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
import ShapeLines.Layers.Plan6Lines
import ShapeLines.Layers.Link12MembersOneToThree
import ShapeLines.Layers.Link12OwnRoundsGuards
import ShapeLines.Layers.Link12MergeRecords
import ShapeLines.Layers.Link12AfterOwnRounds
import ShapeLines.Layers.Link12MembersFiveToEight
import ShapeLines.Layers.Link12Batching
import ShapeLines.Layers.Link12MembersTenToFourteen

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- At every record that publicOfO returns at the stored full-size files: from border169, the
fourteen members 169 to 182 of the run on shapes return border183. -/
theorem layersLink12_runs : RunsAll 169 14 border169 border183 :=
  layersLink_runs Johnson.Unfolds.Layout.lay_size closingHint 12 (by decide) (by decide)
    layersBorders12 layersPlan6_lines
    layersLink12_membersOneToThree
    layersLink12_ownRoundsGuards
    layersLink12_mergeRecords
    layersLink12_afterOwnRounds
    layersLink12_membersFiveToEight
    layersLink12_batching
    layersLink12_membersTenToFourteen

/-- publicOfO returns a record at the stored full-size files, and there, from border169, the
fourteen members 169 to 182 of the run on shapes return border183. -/
theorem layersLink12_runs_at_a_record : ∃ X₀ : OnBytes.Model.Verify.Public,
    VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL
      (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
    (shapeL (LWn X₀)).runFrom 169 14 border169 = .ok border183 :=
  RunsAll.ex Johnson.Unfolds.Layout.lay_size layersLink12_runs

end ShapeLines

#print axioms ShapeLines.layersLink12_runs
#print axioms ShapeLines.layersLink12_runs_at_a_record
