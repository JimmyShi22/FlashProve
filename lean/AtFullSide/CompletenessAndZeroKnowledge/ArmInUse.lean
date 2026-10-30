-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/CompletenessAndZeroKnowledge/ArmInUse.lean: at public files in use honestProvers (E2E/TheHonestProver.lean) is its arm.

1.  WHAT IS CLAIMED: in scope, under the verifier's test on the files, honestProvers is the arm at some description and return,
    by makerReturns and offlineDescriptionNamed and returnIsTheDescription (AtFullSide/K14/Sim/ReturnAtTerm.lean).
    So the fixed-message provers of the term's other arms are not reached there. honestProvers_eq_atReturn is the same fact
    at its own name for the arm.
2.  This file claims nothing of a protocol: this file proves neither completeness nor zero knowledge of the protocol.
-/
import Johnson.CompletenessAndZeroKnowledge.SendsAtTerm
import AtFullSide.Honest.HonestProverLaws
import AtFullSide.K14.Sim.ReturnAtTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Compilation
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest.Term (OnlineReturn returnIsTheDescription makerReturns)
open VerifiableInference.Desc (Chain)
open P5J
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

/-- **At files in use the term is the arm.** -/
theorem honestProvers_arm_in_use (files : PublicFiles) (parts : Parts files) (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) :
    ∃ (description : OfflineDescription) (returned : OnlineReturn files) (places : H2U.Places4)
      (firstChain : Chain TS ProofFile.Cl),
      honestProvers files parts = honestProversGivenDescriptions files parts description returned places firstChain := by
  obtain ⟨description, hOff, -⟩ := offlineDescriptionNamed files live
  obtain ⟨returned, hMaker⟩ := makerReturns files scope live
  obtain ⟨places, firstChain, hPlaces, hChain, -⟩ := returnIsTheDescription files scope live returned hMaker
  exact ⟨description, returned, places, firstChain,
    honestProvers_arm files parts description returned places firstChain hOff hMaker hPlaces hChain⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.honestProvers_arm_in_use
