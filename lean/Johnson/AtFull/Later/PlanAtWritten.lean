-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Later/PlanAtWritten.lean: the tests on the plan pass at the written description, with
the written declared rounds under the name that the statement on the proof file's maker uses
(`Johnson.AtFull.Pub.DW`). One call.

The written declared rounds of a proof file of full size stand in the library under three names with
one body: `Johnson.AtFull.Pub.DW`, `Johnson.AtFull.ProofRows.declProofFull`,
`P2Law.ProofPlan.declProofFull`. `hW_met` (Johnson/AtFull/ProofPlan/DeclSame.lean) stands at the
second. Which of the three stays is not said here.

Limits, as that file says them: at the written description every sub-protocol's own test and fileOk
are the literal true, and the test of the declared rounds against the plan's is true almost by the
way the written description is made. What it does carry to the proof file's description, with hC
and hD: the stored parts' depth, labelsOk, placesOk, beforeOk, treeSharingOk, readsOk, sentFit, sealLast,
and shaped (`planWord_of_cut`, Johnson/AtFull/ProofPlan/WrittenDesc.lean). Nothing on soundness.

-/
import Johnson.AtFull.ProofPlan.DeclSame
import Johnson.AtFull.Pub.PubOfMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Later
open VerifiableInference.PlanWritten (cutFirstFull cutSharedFull cutSecondFull)
open Johnson.AtFull.Pub (DW)

/-- Two names, one term. -/
theorem DW_same : DW = Johnson.AtFull.ProofRows.declProofFull := rfl

/-- **The tests on the plan pass at the written description.** -/
theorem hW_DW :
    (P2Law.ProofPlan.wOf cutFirstFull cutSharedFull cutSecondFull DW 32).planOk = true := by
  rw [DW_same]
  exact Johnson.AtFull.ProofPlan.hW_met

end Johnson.AtFull.Later

#print axioms Johnson.AtFull.Later.DW_same
#print axioms Johnson.AtFull.Later.hW_DW
