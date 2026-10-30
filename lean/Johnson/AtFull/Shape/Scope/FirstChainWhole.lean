-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/FirstChainWhole.lean: first_chain_closed AT THE FIRST CHAIN's SCRIPT firstScriptAt, WITH hL AT THE MEMBER 354
FROM acceptedS_at_first_thread_whole (Honest/K12/AtFile/LotLAcceptedWhole.lean), which speaks at
SaidOk: SaidWalk gives SaidOk. firstScriptAt enters at 354
alone: first_chain_closed and all beneath hold at every parts. hyes comes from the run on shapes at the stored files (yes_of_whole), which is a
premise here (hW); the record at the stored files from record_there.

  first_chain_whole          **yes₁ ∧ carry₁ ∧ AcceptedS at every member**, from the stored run and its tests
  first_chain_whole_honest   the same at the base filling at openHonest: hK is rfl

Limits. CONDITIONAL ON 26 CLOSED FACTS at the stored files: hW, the run on shapes through all 358 members, and the 25 tested runs: if one
fails, the theorem is empty; none is proved here. hW, hT and hTH speak at every record that publicOfO returns; the proof spends them at
record_there's record. NO THEOREM OF THIS LIBRARY SHOWS A STAND OF THIS THREAD AT A BORDER BEYOND 0
BUT FROM A PREMISE THAT HOLDS ONE (ties_at_last, Johnson/Desc/ProofFile/Honest/K14/TiedToEnds.lean:
under the head HeadAtReturn, from a stand of the last chain's thread and the clause TiedToEnds, at
the threads' parts and at letters for what is said, which any value fills). AT BORDER 0
enters_firstThread (Johnson/Desc/ProofFile/Honest/Thread/EntersFirst.lean) SHOWS Thr, WITHOUT WHAT
IS SAID, UNDER THAT HEAD, ready's RETURN, okStart, THE PARSE OF THE REQUEST, ServesAt AND
ScriptTies: each conjunct speaks at stands of ThrS, under no stop, no fall and
the side's having moved: that a run of the honest prover reaches a stand, and that the prover moves, is the work of other files, with owes₁,
the door and the two other chains. It is the column yes₁ of a gather, not «the first chain accepts». NextJ carries nothing new beside
BehindS's Thr and shapeJ_at_first; it stands for FromThreadsJ's field. An implication: the head at a return and the return are premises too;
that they can be met together is not shown here. AT THE BASE FILLING, the crossing not being here, at its own type of random values, at an index that is a letter: NOT AT
THE ONLINE PROVER, whose filling reads this one through the coins' map. Two named hypotheses stand before anything at it counts:
 W's rows ready, the lent o_sp words tied at U and O.
The wide filling is defined in Honest/K1/Law/WSideAtFill.lean. Here it is called the base filling. Nothing on soundness, completeness
or hiding.
-/
import Johnson.AtFull.Shape.Scope.FirstChainClosed
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLAcceptedWhole
import Johnson.AtFull.Shape.Scope.YesOfWhole
import Johnson.Desc.ProofFile.Honest.OpenHonest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (OpenedColumn)
open VerifiableInference.PlanWritten (publicOfO)
open ProofFile.Honest (Coins Mid Local NextJ AcceptedJ AcceptedS shapeJ OnlineProverWithDescription onlineProverFromPublicFiles onlineProverPartsInUse WiderIn
  OnlineProverArguments IndexCommitterCoins Cells SaidWalk fallsBy)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K9 (oneShape)
open OnBytes.HonestTrace (Sz)

variable {files : VerifierAndGoals.PublicFiles} {W₀ : Type} (I : WiderIn W₀) (Op : OnlineProverArguments)
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

set_option maxRecDepth 100000 in
/-- **yes₁, carry₁ AND AcceptedS AT THE FIRST SCRIPT.** -/
theorem first_chain_whole (hK : Op.keyOf = ProofFile.Honest.K5.keyOfK3)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref Op) = .ok A)
    (h : HeadAtReturn files A) (numbers : FallNumbers) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (B : Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → List OpenedColumn → Prop)
    (m₀ : Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)
    {c₀ : ShA} (hW : RunsAll 0 358 startShA c₀)
    (hT : ∀ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ →
      ∀ l, l < 24 → ∃ c : ShA, (shapeL (LWn X₀)).runFrom 0 (14 * l + 10 + 1) startShA = .ok c ∧
        ProofFile.Honest.K9.oneShape c.1 = true)
    (hTH : ∀ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ →
      ∃ c : ShA, (shapeL (LWn X₀)).runFrom 0 (337 + 12) startShA = .ok c ∧
        ProofFile.Honest.K9.oneShape c.1 = true) :
    let parts : FirstThreadParts A :=
      ⟨ProofFile.Honest.K1.firstScriptAt I Sz.ref Op A h.firstChain, numbers⟩
    let J := shapeJ (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))) startShA
    (∀ b, b < (firstThread h parts w).bs.length →
      AcceptedJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀) J
        (fallsBy (firstFalls A numbers) h.description.first.blocksInOrder) b) ∧
    (∀ b, b < (firstThread h parts w).bs.length →
      NextJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀) J
        (fallsBy (firstFalls A numbers) h.description.first.blocksInOrder) b) ∧
    (∀ b, b < (firstThread h parts w).bs.length →
      AcceptedS (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
        (fallsBy (firstFalls A numbers) h.description.first.blocksInOrder) b) := by
  intro parts J
  obtain ⟨Bs, base, O'⟩ := h.head.laid.opened
  have hB := O'.made
  have eG : seatGround A = Bs.G₀ := seatGround_of_base hB
  have eJ : J = shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA := by
    show shapeJ (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))) startShA = _
    rw [eG]
  rw [eJ]
  obtain ⟨X₀, hX₀⟩ := record_there Johnson.Unfolds.Layout.lay_size
  have hyes := Scope.yes_of_whole h.head hB hW
  have hS := ProofFile.Honest.K12.LotL.acceptedS_at_first_thread_whole h I Op hA numbers w
    (fallsBy (firstFalls A numbers) h.description.first.blocksInOrder)
  exact first_chain_closed I Sz.ref Op hK hA h parts w hB B m₀ hyes
    (fun blk hb k s m E ds y cols hTh _ => hS blk hb k s m E ds y cols ⟨hTh.1, hTh.2.1.1⟩) hX₀
    (hT X₀ hX₀) (hTH X₀ hX₀)

variable {I}

set_option maxRecDepth 100000 in
/-- **The same at the base filling at openHonest.** -/
theorem first_chain_whole_honest
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction Sz.ref ProofFile.Honest.openHonest) = .ok A)
    (h : HeadAtReturn files A) (numbers : FallNumbers) (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
    (B : Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → List OpenedColumn → Prop)
    (m₀ : Coins A.B → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)
    {c₀ : ShA} (hW : RunsAll 0 358 startShA c₀)
    (hT : ∀ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ →
      ∀ l, l < 24 → ∃ c : ShA, (shapeL (LWn X₀)).runFrom 0 (14 * l + 10 + 1) startShA = .ok c ∧
        ProofFile.Honest.K9.oneShape c.1 = true)
    (hTH : ∀ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ →
      ∃ c : ShA, (shapeL (LWn X₀)).runFrom 0 (337 + 12) startShA = .ok c ∧
        ProofFile.Honest.K9.oneShape c.1 = true) :
    let parts : FirstThreadParts A :=
      ⟨ProofFile.Honest.K1.firstScriptAt I Sz.ref ProofFile.Honest.openHonest A h.firstChain, numbers⟩
    let J := shapeJ (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))) startShA
    (∀ b, b < (firstThread h parts w).bs.length →
      AcceptedJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀) J
        (fallsBy (firstFalls A numbers) h.description.first.blocksInOrder) b) ∧
    (∀ b, b < (firstThread h parts w).bs.length →
      NextJ (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀) J
        (fallsBy (firstFalls A numbers) h.description.first.blocksInOrder) b) ∧
    (∀ b, b < (firstThread h parts w).bs.length →
      AcceptedS (firstThread h parts w) (SaidWalk (firstThread h parts w) B m₀)
        (fallsBy (firstFalls A numbers) h.description.first.blocksInOrder) b) :=
  first_chain_whole I ProofFile.Honest.openHonest rfl hA h numbers w B m₀ hW hT hTH

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.first_chain_whole
#print axioms Johnson.AtFull.Shape.first_chain_whole_honest
