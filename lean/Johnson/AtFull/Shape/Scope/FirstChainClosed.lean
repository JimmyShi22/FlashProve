-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/FirstChainClosed.lean: first_chain_last WITH THE CLOSED TEST AT THE 25 BORDERS BY THE RUN AT THE STORED
FILES (eqSizesYes_of_tested), AND THE ACCEPTANCE IN THE FORM AcceptedS: at the first thread the family J is no premise
(shapeJ_at_first).

  first_chain_closed   **yes₁ ∧ carry₁ ∧ AcceptedS at every member**

Limits. Conditional: hyes and the stored run's tests hT, hTH are closed facts at the stored files, premises here; hL, no closed fact, is a premise too. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.FirstChainLast
import Johnson.AtFull.Shape.Scope.EqSizesInScope
import Johnson.AtFull.Shape.Scope.ShapeAtFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (OpenedColumn)
open VerifiableInference.PlanWritten (publicOfO)
open P5J (TS)
open ProofFile.Honest (Coins Mid Local NextJ AcceptedJ AcceptedS shapeJ OnlineProverWithDescription onlineProverFromPublicFiles onlineProverPartsInUse WiderIn
  OnlineProverArguments IndexCommitterCoins Cells SaidWalk fallsBy)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K9 (oneShape)

variable {files : VerifierAndGoals.PublicFiles} {W₀ : Type} (I : WiderIn W₀) (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {Bs : ProofFile.PureBase}

set_option maxRecDepth 100000 in
/-- **yes₁, carry₁ AND AcceptedS.** -/
theorem first_chain_closed (hK : O.keyOf = ProofFile.Honest.K5.keyOfK3)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz O) = .ok A)
    (h : HeadAtReturn files A) (parts : FirstThreadParts A) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs)
    (B : Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → List OpenedColumn → Prop)
    (m₀ : Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)
    (hyes : (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)).yes startShA 358 = true)
    (hL : AcceptedJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
      (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
      (fallsBy (firstFalls A parts.numbers) h.description.first.blocksInOrder) (353 + 1))
    {X₀ : Verify.Public}
    (hX₀ : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
    (hT : ∀ l, l < 24 → ∃ c : ShA, (shapeL (LWn X₀)).runFrom 0 (14 * l + 10 + 1) startShA = .ok c ∧
      oneShape c.1 = true)
    (hTH : ∃ c : ShA, (shapeL (LWn X₀)).runFrom 0 (337 + 12) startShA = .ok c ∧
      oneShape c.1 = true) :
    (∀ b, b < (firstThread h parts w).bs.length →
      AcceptedJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
        (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
        (fallsBy (firstFalls A parts.numbers) h.description.first.blocksInOrder) b) ∧
    (∀ b, b < (firstThread h parts w).bs.length →
      NextJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
        (shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA)
        (fallsBy (firstFalls A parts.numbers) h.description.first.blocksInOrder) b) ∧
    (∀ b, b < (firstThread h parts w).bs.length →
      AcceptedS (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
        (fallsBy (firstFalls A parts.numbers) h.description.first.blocksInOrder) b) := by
  obtain ⟨y, n⟩ := first_chain_last I Sz O hK hA h parts w hB B m₀ hyes hL
    (fun l hl => Scope.eqSizesYes_of_tested h.head hB hX₀ (by omega) (hT l hl))
    (Scope.eqSizesYes_of_tested h.head hB hX₀ (by omega) hTH)
  have hlen : (firstThread h parts w).bs.length = 358 := flat_len h.head
  refine ⟨y, n, fun b hb blk hblk k s m E ds yy cols hTh => ?_⟩
  exact y b hb blk hblk k s m E ds yy cols hTh
    (Scope.shapeJ_at_first h parts w hB hyes (by omega) hTh.1)

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.first_chain_closed
