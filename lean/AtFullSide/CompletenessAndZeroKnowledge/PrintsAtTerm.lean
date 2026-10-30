-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/CompletenessAndZeroKnowledge/PrintsAtTerm.lean: the arms of the honest provers (E2E/TheHonestProver.lean) print.

1.  WHAT IS CLAIMED: at every arm under refusal the two strategies meet StratLaw at the run values of their coins: TermPrints, by the law at the arm
    (AtFullSide/Honest/StratLawAtTerm.lean). Refusal moves no strategy.
2.  This file claims nothing of a protocol: this file proves neither completeness nor zero knowledge of the protocol.
-/
import AtFullSide.CompletenessAndZeroKnowledge.ParserAtTerm
import AtFullSide.Honest.StratLawAtTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 20000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve FlashProve OnBytes.FrontRoad OnBytes.WholeKey OnBytes.Prover
open VerifiableInference.OnPublicFiles AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest.Term (OnlineReturn)
open VerifiableInference.Desc (Chain)
open P5J
open Johnson.Face
open IntegerTransformer (Settings)

/-- Given by hand, as in E2E/TheHonestProver.lean. -/
local instance (priority := high) printsAtRunValueNonempty : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) printsAtPurseNonempty (l : List (ProofFile.Honest.Addr × ProofFile.Honest.Due)) : Nonempty (ProofFile.Honest.Purse l) :=
  ⟨ProofFile.Honest.Purse.any l⟩

/-- At any provers: the law at the two strategies prints; refusal moves no strategy. -/
theorem armPrintsRefuse_of_laws (settings : Settings) (files : PublicFiles)
    (Tr : (flashProveDescription.input files allZeroDigest []).Index → (flashProveDescription.input files allZeroDigest []).Instance → Prop)
    (provers : HonestProvers (FlashProtocol files)) (Served : (flashProveDescription.C files).I → (flashProveDescription.C files).X → Prop)
    (runsT : provers.offlineProver.Coin → ByteArray × ByteArray)
    (runsB : provers.onlineProver.Coin → ByteArray × ByteArray)
    (hT : ∀ w x κ, Johnson.Prover.Print.StratLaw (_root_.Run.ckP .two) ((flashS files).DK.at OnBytes.Slice.frS.P.T.a)
      (OnBytes.Flat.front₀ (flashS files).G.rec₀) (OnBytes.Flat.join₀ (flashS files).G.rec₀) ByteArray.empty
      (provers.offlineProver.strat w x κ) (runsT κ).1 (runsT κ).2)
    (hB : ∀ w a κ, Johnson.Prover.Print.StratLaw (_root_.Run.ckP .two) ((flashS files).DP.at OnBytes.Slice.frS.P.T.a)
      (OnBytes.Flat.front₀ (flashS files).G.z₀.2) (OnBytes.Flat.join₀ (flashS files).G.z₀.2) ByteArray.empty
      (provers.onlineProver.strat w a κ) (runsB κ).1 (runsB κ).2) :
    ArmPrintsRefuse settings files Tr provers Served runsT runsB := fun _ =>
  { T := fun _ _ _ κ _ => hT _ _ κ
    B := fun _ _ _ _ _ κ _ => hB _ _ κ }

variable (parts : (files : PublicFiles) → Parts files) (files : PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp)

set_option maxHeartbeats 2000000 in
/-- **The arms of the honest provers print.** -/
theorem termPrints : TermPrints parts files hr := fun d r p c _ =>
  armPrintsRefuse_of_laws (settingsOfRead pp) files (Seam.servedAt files hr)
    (HonestProvers.ofThreeProvers (honestProversGivenDescriptions files (parts files) d r p c)) (Seam.servedAt files hr)
    (rvKey (parts files).book runValueBytes runValueBytes) (fun κ => (runValueBytes κ.1.2, runValueBytes κ.2.2))
    (fun w x κ => offlineAt_stratLaw (parts files) d w x κ)
    (fun w a κ => onlineAt_stratLaw r p c w.2.2.2 (w.1, w.2.1, w.2.2.1) a κ)

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.termPrints
