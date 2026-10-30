-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotDoorAsksFirstLaid.lean: WHAT THE LAST CHAIN's DOOR ASKS OF THE FIRST CHAIN (AtPublicFiles.KeyLastChain.DoorAsks, E2E/KeyLastTerm.lean: one run, one state, the field, the letter's next), AT ITS LAST
BORDER 19, AT THE LAID THREAD AND LETTER, WITH NO PREMISE LEFT ON ANY MEMBER.

  LotDoorAsksFirstLaid, lotDoorAsksFirstLaid   DoorAsks (laidFirst Z d K₀ w x) (laidSaid Z d K₀ w x) 19, AT EVERY INPUT, from: the offline description is returned, in scope, protocolDataWellFormed,
                         fullPub = some K₀

BY WHAT. lotDoorAsksFirstThree (E2E/LotFieldFirstMeets.lean) with PlaysS at 4 and 10 by lookupsFive_laid (E2E/LotWitnessReads.lean) and at 15 by fiveAtRanges (E2E/LotFiveAtRanges.lean);
FirstPublic and NoStop at the value.

What it does not say. NO STAND of the thread at 19 is shown here: where there is none, state and field are empty. It stands on whatever these three stand on. Nothing on acceptance. Nothing on
soundness, completeness, hiding or binding. No law over coins.
-/
import E2E.LotDoorAsksOwn
import E2E.LotFieldFirstMeets
import E2E.LotJoinLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.FirstH.Lots
open VerifiableInference.Desc.Key (Xi)
open AtPublicFiles.AtFiles (FullSizeMatrix protocolAtFiles)
open AtPublicFiles.AtFiles.HonestTerm (OfflineDescription offlineDescription matrixReader sourced_of_ok)
open AtPublicFiles.KeyStandWalked (offlineValue)
open AtPublicFiles.KeyBook (KeyPub fullPub)
open AtPublicFiles.KeyValueHolds (noStop_value)
open AtPublicFiles.LotField (doorAsks_own)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)
open ProofFile.Honest

variable (Z : PublicFiles) (d : OfflineDescription) (K₀ : KeyPub)

/-- **What the door asks of the first chain, laid: no premise on a member.** -/
def LotDoorAsksFirstLaid : Prop :=
  offlineDescription Z = .ok d → InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true → fullPub = some K₀ →
    ∀ (w : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed) (x : Xi),
      AtPublicFiles.KeyLastChain.DoorAsks (laidFirst Z d K₀ w x) (laidSaid Z d K₀ w x) 19

theorem lotDoorAsksFirstLaid : LotDoorAsksFirstLaid Z d K₀ := by
  intro hd scope live hK w x
  have hs := sourced_of_ok live hd
  refine doorAsks_own (lotDoorAsksFirstThree K₀ d.source d.numbers d.later (offlineValue (files := Z) d)
    matrixReader (laterValue Z d K₀) w.1 w.2.1 x hs scope hK (firstPublic_atValue hs scope)
    (noStop_value _ _ _ _ _ _ _ _ _ _ _ _ _).1 ?_).1
  intro b hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · exact (lookupsFive_laid hs scope hK _ (fun _ _ _ => none) 4 (by decide)).plays
  · exact (lookupsFive_laid hs scope hK _ (fun _ _ _ => none) 10 (by decide)).plays
  · exact (fiveAtRanges d (laterValue Z d K₀) w.1 w.2.1 x hs scope hK rfl _ (fun _ _ _ => none)).plays

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.lotDoorAsksFirstLaid
