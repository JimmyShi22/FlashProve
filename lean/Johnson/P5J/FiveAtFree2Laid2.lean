-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/FiveAtFree2Laid2.lean: THE TOWER's FIVE ROWS THAT ARE LAWS AT THE TWO CLOSED VALUES,
WHERE THE PROOF FILE's LIST OF ENTRY TESTS IS THE ONE THAT ProofAsksFirstThirteenTests.lean PINS (LPFD.lawsAsk,
Johnson/Desc/Laid/ProofAsks.lean, thirteen rows): ONE PREMISE IS LEFT BESIDE THE HEAD AND THE GATE's
ACCEPT. THE THEOREM DEPENDS ON ThirdParty/ (GAPS.md). One theorem: A JOINING: no weight of its own.

WHICH VERIFIER. THE PROOF CALLS A LAW ON ROW 9 OF THE LIST (`LPFD.asks_made_at`). The head h names
the list by name, so h SAYS MORE than a yes of the list's first eight rows: two rows of tests that
compare with written values stand in h. A statement that is proved from this file speaks of a
verifier that asks the thirteen rows. THE PRICE IS PAID IN WHETHER THE HEAD CAN BE MET.
[The list has fourteen rows: the thirteen and one more
(Johnson/Desc/Laid/ProofAsks.lean): so the head says that much more.]

  **five_at_free2_laid2**   the head · the gate's accept · last → h.Five h.free (depthZ Z)
    head_cuts · shared_joint_count   as in five_at_free (Johnson/P5J/FiveAtFree.lean), the test
                 guard := LPFD.asks_made_at h.laid.asks h.laid.pub
    reply_leaves as there
    leads3_last_chains_table   h.leads3_of_leftAt last (Johnson/P5J/L0/LastLeftAt.lean): no letter
    tables_fit   ThreeF.tables_fit (three_at_free_head_alone h)
                 (Johnson/P5J/ThreeAtFreeHeadAlone.lean): no premise but the head
LEFT:
  last   h.LastLeftAt: the last chain's row's own list: proved in Johnson/P2LawR/LastLeftAlone.lean
Limits. A member of the head is proved at `VerifierAndGoals.storedPublicFiles` alone (`headMember_zFull`, AtFullSide/Top/,
a side library); last follows from the head. FOUR ROWS ARE WORTH WHAT THE HEAD IS WORTH. The full
size alone (the written values). At OnBytes.secondHashFunction alone. No soundness statement. Nothing on hiding.
-/
import Johnson.P5J.FiveAtFreeLaid2
import Johnson.P5J.L0.LastLeftAt
import Johnson.P5J.ThreeAtFreeHeadAlone

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace P5J

open OnBytes OnBytes.Flat OnBytes.Maker
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (pinnedAt_of_row)
open VerifierAndGoals FlashProve FlashProve VerifierAndGoals.AtTheName

variable {Z : VerifierAndGoals.PublicFiles} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option maxHeartbeats 8000000 in
/-- **THE FIVE ROWS AT THE TWO CLOSED VALUES. ONE PREMISE, `last`, PROVED IN LastLeftAlone.lean.**
-/
theorem five_at_free2_laid2
    (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x)
    (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) (last : h.LastLeftAt) : h.Five h.free (depthZ Z) :=
  h.five_mk h.free (depthZ Z)
    (VerifiableInference.Desc.Kinds.Head.Law.head_cuts_of_guard h
      (LPFD.asks_made_at h.laid.asks h.laid.pub))
    (reply_leaves_at_mg h.toAtMg h.free h.free_q₁ h.free_q₂ h.free_q₃ _)
    (_root_.Desc.K14.Law.k14_at_free_head h
      (pinnedAt_of_row (LPFD.asks_made_at h.laid.asks h.laid.pub)) (depthZ Z)
      (slots_le_the Z h.scope hl) _ _ _ _ _ _ _)
    (h.leads3_of_leftAt last)
    (ThreeF.tables_fit (three_at_free_head_alone h))

end P5J

#print axioms P5J.five_at_free2_laid2
