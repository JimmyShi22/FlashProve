-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/FirstArmsTables.lean: What the first thread's tables of trees 1 and 82 are, at
the first chain's Script, the arms of FirstArms (K12/AtFile/WJointArms.lean): tree 1 is tree 1 of the
opening's job, tree 82 is tree 0 of W's job; each fixed right behind the rounds in front of its
sending.

Limits. Under the head, a hypothesis. Nothing on soundness, completeness or hiding.
-/
import AtFullSide.K1.FirstScript
import AtFullSide.K12.FirstArmsK1
import Johnson.Desc.K1.Law.TiesAtAll
import Johnson.Desc.ProofFile.Honest.K1.Law.SeatsAtW
import Johnson.Desc.ProofFile.Honest.K1.Law.SeatsAtTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The arm of tree 82**: W's job's tree 0. -/
theorem arm_w (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀) :
    (∀ k v hd, (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread.table (.own 82) k v hd = treeTbl 0 (witB I A.Z) (jobWAt Op A.Z A.G) () 0 k v hd) ∧
      (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread.fixed (.own 82) = roundsTo cF.blocksInOrder 356 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e : treesTo cF.blocksInOrder 356 = 82 := (nums_w h O).2
  have hj : 0 < (jobWAt Op A.Z A.G).P.trees.length := by
    have ew : VerifiableInference.Desc.K1.parWZ A.Z VerifiableInference.Desc.K13.Law.wMsgFull =
        VerifiableInference.Desc.K1.parWF := VerifiableInference.Desc.K1.eW_atAll h O (VerifiableInference.Desc.K1.pin1_atAll h)
    show 0 < (VerifiableInference.Desc.K1.parWZ A.Z VerifiableInference.Desc.K13.Law.wMsgFull).trees.length
    rw [ew]
    exact AtFullSide.K12.cols_written.2.2.2.2.2.1
  have hO := ownTrees_first_w h hA test carryX item n₁ n₂ b₀ Vd Rd Kp w (I := I) (S := S) (Op := Op)
  have t := hO.table 0 hj
  have f := hO.fixed 0 hj
  have eb : (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
    w).thread.bs = cF.blocksInOrder := rfl
  rw [eb, e] at t f
  refine ⟨t, f.trans ?_⟩
  show 0 + roundsTo cF.blocksInOrder 356 + 0 = roundsTo cF.blocksInOrder 356
  omega

/-- **The arm of tree 1**: the opening job's tree 1. -/
theorem arm_two (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : LocB W₀ → Prop) (Rd : Nat → LocB W₀ → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : LocB W₀) :
    (∀ k v hd, (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread.table (.own 1) k v hd = treeTbl 0 (witB I A.Z) (jobTwoAt S A.Z A.G) () 1 k v hd) ∧
      (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
        w).thread.fixed (.own 1) = roundsTo cF.blocksInOrder 2 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have e : treesTo cF.blocksInOrder 2 = 0 := trees_two h O (treesNo_atN A.Z cF VerifiableInference.Desc.K1.place_two)
  have hj : 1 < (jobTwoAt S A.Z A.G).P.trees.length := by
    obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
    have eg : VerifiableInference.Desc.K1.firstPar Bs.G₀.first (VerifiableInference.Desc.K1.gpOf A.Z) =
        VerifiableInference.Desc.K1.parGF := VerifiableInference.Desc.K1.eG_atAll h O (VerifiableInference.Desc.K1.pin1_atAll h)
    show 1 < (VerifiableInference.Desc.K1.firstPar A.G.first (VerifiableInference.Desc.K1.gpOf A.Z)).trees.length
    rw [eG, eg]
    exact AtFullSide.K12.cols_written.2.2.2.2.1
  have hO := ownTrees_first_two h hA test carryX item n₁ n₂ b₀ Vd Rd Kp w (I := I) (S := S) (Op := Op)
  have t := hO.table 1 hj
  have f := hO.fixed 1 hj
  have eb : (lettersHead h A.H (firstScriptAt I S Op A cF) test carryX item n₁ n₂ b₀ Vd Rd Kp
    w).thread.bs = cF.blocksInOrder := rfl
  rw [eb, e] at t f
  refine ⟨t, f.trans ?_⟩
  show 0 + roundsTo cF.blocksInOrder 2 + 0 = roundsTo cF.blocksInOrder 2
  omega

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.arm_w
#print axioms ProofFile.Honest.K1.arm_two
