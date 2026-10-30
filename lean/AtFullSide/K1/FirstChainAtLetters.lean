-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/FirstChainAtLetters.lean: first_chain_at_sockets (AtFullSide/K1/FirstChainAtSockets.lean) AT THE NAMES OF AtFullSide/Honest/TheLettersFirst.lean:
thread₁, said₁, falls₁, numbers, J₁. The step costs nothing: first h is the Script at numbers h, by its definition; hB and hW come off the fields of OpenFiles.

  first_chain_at_letters   yes₁ ∧ carry₁ at all 358 members
  startJ_at_letters        J₁ at the first state, from startFit

Limits. Those of first_chain_whole: CONDITIONAL ON 26 CLOSED FACTS at the stored files (OpenFiles' shapesToEnd, hT, hTH); F is a premise, and that an OpenFiles exists at the base filling is not said here; no stand is known without a premise; at the base
filling; the crossing is another's. This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.Honest.TheLettersFirst
import AtFullSide.K1.FirstChainAtSockets

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtFullSide.Honest.TheLetters
open ProofFile.Honest ProofFile.Honest.FirstThread
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Scope
open ProofFile.Honest.Term (matrixInput)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open OnBytes (TableKey)
open VerifiableInference.PlanWritten (publicOfO)
open OnBytes.Model (Verify.Public)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

theorem first_chain_at_letters
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    (h : HeadAtReturn files A) (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit)
    (F : OpenFiles A)
    (hT : ∀ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ →
      ∀ l, l < 24 → ∃ c : ShA, (shapeL (LWn X₀)).runFrom 0 (14 * l + 10 + 1) startShA = .ok c ∧
        ProofFile.Honest.K9.oneShape c.1 = true)
    (hTH : ∀ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ →
      ∃ c : ShA, (shapeL (LWn X₀)).runFrom 0 (337 + 12) startShA = .ok c ∧
        ProofFile.Honest.K9.oneShape c.1 = true) :
    (∀ b, b < (thread₁ h R).bs.length →
      AcceptedJ (thread₁ h R) (said₁ h R) (J₁ h F) (fallsBy (falls₁ h) h.description.first.blocksInOrder) b) ∧
    (∀ b, b < (thread₁ h R).bs.length →
      NextJ (thread₁ h R) (said₁ h R) (J₁ h F) (fallsBy (falls₁ h) h.description.first.blocksInOrder) b) :=
  first_chain_at_sockets hA h (numbers h) R F.seat
    (runsAll_of_ex ⟨F.publicAtFiles, F.publicData, (run_is_from _ _ _).symm.trans F.shapesToEnd⟩) hT hTH

/-- **J₁ at the first state.** -/
theorem startJ_at_letters (h : HeadAtReturn files A) (F : OpenFiles A) (x : ProofFile.Inst)
    (hx : h.description.okStart x = true) :
    J₁ h F 0 (h.description.start₁ (h.description.pub x)) :=
  startJ_at_sockets h x hx F.base

end AtFullSide.Honest.TheLetters

#print axioms AtFullSide.Honest.TheLetters.first_chain_at_letters
#print axioms AtFullSide.Honest.TheLetters.startJ_at_letters
