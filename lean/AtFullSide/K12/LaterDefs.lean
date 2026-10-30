-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/LaterDefs.lean: the definitions of the shared chain's letters at the base prover, alone,
so that TheLetters imports no law of the tests.

  keepsAtBase      the keeps at the two tests' places; elsewhere a letter.
  readsBase        the base prover's readers.
  laterBase        a value of LaterLetters at the base prover.
  laterTerm        that value with no rider.
-/
import AtFullSide.K12.LaterJobs
import Johnson.Desc.ProofFile.Honest.Thread.TheLaterThreads
import Johnson.AtFull.ProofPlan.WP
import E2E.TheHonestProver

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place Grows)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K1 (SmpStay)
open VerifiableInference.Desc.K12 (P12)
open Desc.K14 (St)
open ProofFile.Honest.K14 (randNow)
open ProofFile.Honest.K12.AtFile (keepsU jobDoorU jobDoorO tableShared fixedShared)
open ProofFile.Honest.K12.AtProof (fourOf placeU)
open ProofFile.Honest.FirstThread
open P2Law.ProofPlan (declProofFull)

/-- The keeps at the two tests' places. -/
def keepsAtBase (Np : H2U.Places4) (Kp₁ : Place → St → St → Prop) : Place → St → St → Prop :=
  fun p s s' =>
    if p = placeU then keepsU (fourOf Np).U s s'
    else if p = ⟨2, none, 10, .K12⟩ then Grows s.st s'.st ∧ SmpStay s.st s'.st
    else Kp₁ p s s'

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- The base prover's readers. -/
def readsBase (h : HeadAtReturn files A) : IndexReaders FullSizeMatrix IndexCommitterCoins :=
  ⟨matrixInput.weights A.Z, randNow (K1.qAt A.Z h.places)⟩

/-- **A value of LaterLetters at the base prover.** bs: the eight sub-protocols. pO: the place's
numbers of the test on G_omega. -/
def laterBase (h : HeadAtReturn files A) (bs : List (Block St Unit)) (pO : P12)
    (rest : Coins A.B → Common FullSizeMatrix IndexCommitterCoins TableKey → List Fmt.Drawn → WtShared)
    (riders : List (RiderCl (Common FullSizeMatrix IndexCommitterCoins TableKey) St)) (Kp₁ : Place → St → St → Prop) :
    LaterLetters A where
  rest := rest
  table := tableShared (K1.qAt A.Z h.places) (readsBase h).weights (readsBase h).rand
    (jobDoorU (X₀ := Unit) A.Z h.places bs A.H.storedWords (readsBase h).weights
      (readsBase h).rand).toRun.toTest
    (jobDoorO (X₀ := Unit) A.Z h.places pO bs (readsBase h).weights (readsBase h).rand).toRun.toTest ()
  fixed := fixedShared declProofFull.2.1
  riders := riders
  keeps := keepsAtBase h.places Kp₁

/-- **The value of LaterLetters with no rider.** -/
abbrev laterTerm (h : HeadAtReturn files A) (bs : List (Block St Unit)) (pO : P12)
    (rest : Coins A.B → Common FullSizeMatrix IndexCommitterCoins TableKey → List Fmt.Drawn → WtShared)
    (Kp₁ : Place → St → St → Prop) : LaterLetters A :=
  laterBase h bs pO rest [] Kp₁

end ProofFile.Honest.Term
