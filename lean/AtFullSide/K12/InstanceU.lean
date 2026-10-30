-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/InstanceU.lean: the test on G_u of the proof file's shared chain at the base prover
itself, the maker's return at the online filling before it is read through.

  half_at_base   the base prover's shared list finds the test's half, at the job of its own stored
                 columns, its index's reader and its plain coins.

Limits. At the base return. Nothing on what the half plays; nothing on completeness, on soundness or
on what is hidden.
-/
import E2E.ThruAtTerm
import Johnson.Desc.ProofFile.Honest.K12.AtFile.HalfAtBase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles
open OnBytes (TableKey)
open OnBytes.Means (InOrder)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.Shared (MeaningS NumbersS)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St blocks)
open ProofFile.Honest.K14 (mgWords form2 WitLens holds2 witL kp2)
open ProofFile.Honest.K12 (proverSideOfProximityTest)
open ProofFile.Honest.K12.AtFile (jobDoorU half_found)
open ProofFile.Honest.K12.AtProof (fourOf placeU randAt sharedWithUO storedWords_at_pure)
open ProofFile.Honest.K12.Light (sentOf)
open ProofFile.Honest.SharedThread (lettersShared)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **The base prover's shared list finds the test's half.** -/
theorem half_at_base (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) (eZ : A.Z = Zp) :
    (A.H.shared.find? fun g => g.place == (fourOf Np).U.place) =
      some (proverSideOfProximityTest (jobDoorU (X₀ := Unit) Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] A.H.storedWords
                         (matrixInput.weights Zp) (randAt (K1.qAt Zp Np))).toRun.toTest) := by
  have e₁ : A.H.shared = sharedWithUO matrixInput A.Z :=
    congrArg (fun A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit => A₀.H.shared) (eq_ofFill base)
  have e₂ : A.H.storedWords = fun w rc i x =>
      (Bind.ForProver.encW Zp (matrixInput.weights Zp w) rc i x).map (·.map OnBytes.Slice.ofF) := by
    funext w rc i x
    rw [storedWords_at_pure base w rc i x, eZ]
    rfl
  rw [e₁, e₂, eZ]
  exact half_found h hA matrixInput b1 b2 b3 b4 b5 b6 b7 b8 hb

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.half_at_base
