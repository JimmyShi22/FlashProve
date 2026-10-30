-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OwnSendersAt.lean: `OwnSenders` (OwnJob.lean) holds at parts whose plans are
the verifier's own, in scope: that one premise can be met at these plans. Of the others nothing is said here.

  `ownSenders_of_plans`   from K.idx.P = parIdx Xs, K.w.P = parW Xs msg, K.send.P = the shared chain's parameters and
                          the two rides as the key's book lays them

By what. `six_sourced`: in scope the one-time numbers are the written ones. `par_sourced`.

Limits. The five equations are premises on K. Nothing on what the parts' data read. Nothing on completeness,
soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OwnJob
import Johnson.RunOne.KeyMsgAll
import E2E.KeyShapeSharedTies

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtKey
open VerifiableInference.Desc.Key (Source LaterPlaces sendingPar sharedPar beforeSharedPoint)
open VerifiableInference.Desc.K1 (Par)
open Johnson.RunOne.KeySendGood (parIdx parW)
open AtPublicFiles.AtFiles (KeySourced SF)
open AtPublicFiles.AtFiles.Full (QK)
open AtPublicFiles.KeyBook (rideW)
open AtPublicFiles.KeyLay (parIK parWK)
open AtPublicFiles.KeyFile (KeyParts)

variable {W₀ Rc X₀ X Wk : Type} {K : KeyParts W₀ Rc X₀ X Wk} {Z : VerifierAndGoals.PublicFiles} {Xs : Source}
  {Nr : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **`OwnSenders` at the verifier's plans.** -/
theorem ownSenders_of_plans (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    {msg : Array OnBytes.OracleNotice} (hm : OnBytes.linMessageW Xs.Y.k.oneTime.lin = some msg)
    (hI : K.idx.P = parIdx Xs) (hIr : K.idx.ride = fun _ => none)
    (hW : K.w.P = parW Xs msg) (hWr : K.w.ride = rideW)
    (hQ : K.send.P = sharedPar Xs.chains (beforeSharedPoint Pl)) : OwnSenders K := by
  have h6 := AtPublicFiles.AtFiles.Full.six_sourced hs scope
  have hlin : Xs.Y.k.oneTime.lin = SF := h6.lin
  have hcf : Xs.Y.k.oneTime.codes = Lk6.AtPlan.keyFull.codes := h6.codes
  have hin : Xs.Y.k.oneTime.indexMasks = Lk6.AtPlan.keyFull.once.input := h6.indexMasks
  have eI : (parIdx Xs).sent = #[Xs.Y.k.oneTime.indexMasks] := by
    simp [parIdx, Par.sent, sendingPar]
  have eW : (parW Xs msg).sent = msg := by
    simp [parW, Par.sent, sendingPar]
  have eI' : parIK.sent = #[Lk6.AtPlan.keyFull.once.input] := by
    simp [parIK, Par.sent]
  have eW' : parWK.sent = (OnBytes.linMessageW SF).getD #[] := by
    simp [parWK, Par.sent]
  refine ⟨?_, ?_, hIr, ?_, ?_, hWr, ?_⟩
  · rw [hI, eI, eI', hin]
  · rw [hI]
    exact hcf
  · rw [hW, eW, eW', ← hlin, hm]
    rfl
  · rw [hW]
    exact hcf
  · rw [hQ]
    exact AtPublicFiles.AtFiles.Full.par_sourced hs scope

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.ownSenders_of_plans
