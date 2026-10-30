-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/PlanOwnersInScope.lean

The two public hypotheses of the lookup's honest side at the full size, "PlanOwners X"
(Johnson/Desc/ProofFile/Honest/K3/Law/WitOwnerFull.lean) and "PlanLabels X"
(Johnson/Desc/ProofFile/Honest/K3/WitPlan.lean), for public files in the goals' scope. Two theorems;
no definition. This file states no goal.

Main theorems, under the three premises on the public files (Z is in the goals' scope; the goals'
reader returns pp; "publicOf" returns X):
* "planOwners_in_scope": "PlanOwners X": at each of the 25 links the list of where the matrices are
  read, made of the plan's own marks ("matsOwn"), is the list that goes by the matrices' names
  ("matsOf").
* "planLabels_in_scope": "PlanLabels X": attention links, twelve groups, and at each of the 25 links
  the names of the plan's list are the labels.

Each is one call of Johnson/HonestTrace/PlanLabelsOfMarks.lean ("planOwners_of_marks",
"planLabels_of_marks") at "planMarks_in_scope" (Johnson/Goal/HonestTrace/PlanMarksInScope.lean) and
"partsFit_in_scope" (Johnson/Goal/HonestTrace/FromCellsInScope.lean).

Limits. The full size and the goals' scope alone. That "publicOf" returns is a premise: no theorem
of this file shows public files that meet the three premises together. At "VerifierAndGoals.storedPublicFiles", with lay
:= some VerifierAndGoals.storedPublicFiles.lay, each of the three is a theorem elsewhere: "VerifierAndGoals.inScope_full"
(Johnson/Goal/Files/ScopeExample.lean), "VerifierAndGoals.filesRead" (Johnson/Goal/Files/FilesReadProof.lean)
and, in the side library, "publicOf_zFull_returns" (AtFullSide/Planner/PublicReturns.lean); none of
them is called here. Both hypotheses are public: they read the verifier's plans and no trace. All
limits of Johnson/HonestTrace/PlanLabelsOfMarks.lean hold here: among them, nothing is said on what
a reader of cells answers under an owner's segment and name.

Not claimed: anything on a prover, on what a verifier accepts, or on a property of the protocol.
-/
import Johnson.HonestTrace.PlanLabelsOfMarks
import Johnson.Goal.HonestTrace.PlanMarksInScope
import Johnson.Desc.ProofFile.Honest.K3.Law.WitOwnerFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open OnBytes.Model.Verify (publicOf)

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- Under the three premises on the public files: "PlanOwners X". -/
theorem planOwners_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : ProofFile.Honest.K3.PlanOwners X :=
  planOwners_of_marks (planMarks_in_scope hZ hR h) (partsFit_in_scope hZ hR h)

/-- Under the three premises on the public files: "PlanLabels X". -/
theorem planLabels_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) : ProofFile.Honest.K3.PlanLabels X :=
  planLabels_of_marks (planMarks_in_scope hZ hR h) (partsFit_in_scope hZ hR h)

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.planOwners_in_scope
#print axioms OnBytes.HonestTrace.planLabels_in_scope
