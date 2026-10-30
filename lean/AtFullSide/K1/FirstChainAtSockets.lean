-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/FirstChainAtSockets.lean: first_chain_whole_honest (Johnson/AtFull/Shape/Scope/FirstChainWhole.lean) IN THE LETTERS OF THE ONE OBJECT's
FIELDS yes₁, carry₁ AND startJ (AtFullSide/Honest/ThreadsAtTheTerm.lean, ThreadFields): at threadOne, saidOne, the shapes at base.G₀ and the falls
firstFalls A numbers, written out as AtTheSockets.lean writes them.

  first_chain_at_sockets   yes₁ ∧ carry₁ at all 358 members
  startJ_at_sockets        J₁ at the first state, from hx, the field startFit

Limits. Those of first_chain_whole: CONDITIONAL ON 26 CLOSED FACTS at the stored files (hW, hT, hTH); no stand is known without a premise; at the base
filling; the crossing is another's. This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.Honest.TheThreeThreads
import Johnson.AtFull.Shape.Scope.FirstChainWhole
import E2E.FirstBegun

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Scope
open ProofFile.Honest.Term (matrixInput)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open OnBytes (TableKey)
open VerifiableInference.PlanWritten (publicOfO)
open OnBytes.Model (Verify.Public)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

theorem first_chain_at_sockets
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    (h : HeadAtReturn files A) (numbers : FallNumbers)
    (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit)
    {base : ProofFile.PureBase} (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok base)
    {c₀ : ShA} (hW : RunsAll 0 358 startShA c₀)
    (hT : ∀ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ →
      ∀ l, l < 24 → ∃ c : ShA, (shapeL (LWn X₀)).runFrom 0 (14 * l + 10 + 1) startShA = .ok c ∧
        ProofFile.Honest.K9.oneShape c.1 = true)
    (hTH : ∀ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ →
      ∃ c : ShA, (shapeL (LWn X₀)).runFrom 0 (337 + 12) startShA = .ok c ∧
        ProofFile.Honest.K9.oneShape c.1 = true) :
    let first : FirstThreadParts A :=
      ⟨ProofFile.Honest.K1.firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref openHonest A h.firstChain, numbers⟩
    let J := shapeJ (firstZA (Tab.g A.Z base.G₀) (Tab.vals A.Z base.G₀)) startShA
    (∀ b, b < (threadOne h first R).bs.length →
      AcceptedJ (threadOne h first R) (saidOne h first R) J
        (fallsBy (firstFalls A numbers) h.description.first.blocksInOrder) b) ∧
    (∀ b, b < (threadOne h first R).bs.length →
      NextJ (threadOne h first R) (saidOne h first R) J
        (fallsBy (firstFalls A numbers) h.description.first.blocksInOrder) b) := by
  intro first J
  have k := first_chain_whole_honest hA h numbers R.own BaseNil (firstStand A.H R) hW hT hTH
  have eJ : J = shapeJ (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))) startShA := by
    show shapeJ (firstZA (Tab.g A.Z base.G₀) (Tab.vals A.Z base.G₀)) startShA = _
    rw [seatGround_of_base hB]
  rw [eJ]
  exact ⟨k.1, k.2.1⟩

/-- **J₁ at the first state.** -/
theorem startJ_at_sockets (h : HeadAtReturn files A) (x : ProofFile.Inst)
    (hx : h.description.okStart x = true) (base : ProofFile.PureBase) :
    shapeJ (firstZA (Tab.g A.Z base.G₀) (Tab.vals A.Z base.G₀)) startShA 0
      (h.description.start₁ (h.description.pub x)) :=
  AtPublicFiles.Start.first_at_start h.head x hx _ _

end AtFullSide.Honest

#print axioms AtFullSide.Honest.first_chain_at_sockets
#print axioms AtFullSide.Honest.startJ_at_sockets
