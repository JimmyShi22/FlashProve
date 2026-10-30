-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Skeleton/LiveOfReturns.lean: in the goals' scope the test `protocolDataWellFormed`
(Johnson/Goal/Description/Live.lean) accepts wherever its three makers return a value and the two
depths in the returned list of rounds are small.

`protocolDataWellFormed` has seven conjuncts. Three say that a maker returns a value: `thePlanLaid`, `theKeyLaid`,
`theProofLaid`. Four are tests on the values returned. This file pays the four.

How. In scope the returned data of the key file and of the proof file are the written data
(`laid_data_written`, Johnson/Goal/Numbers/KeySeatLaidAt.lean; `laidPOf_written`,
Johnson/Desc/Laid/ProofFullScope.lean). At the written data Lean's kernel has evaluated the tests
(Johnson/Flat/Dec/FitAtWritten.lean).

Main names:
  `kf_written`: the number of blocks at the written data is 24086.
  `listsFull_written`: none of the six written lists of rounds is empty.
  `liveOf_written`: the four tests accept at the written data, at every G whose two depths add up to
    at most 332598 (2 ^ 20 - 715978).
  `theLive_of_returns`: the statement above.

What is not claimed. THAT ANY OF THE THREE MAKERS RETURNS A VALUE AT ANY FILES: so this is no
example that `protocolDataWellFormed` accepts anywhere. The bound on the two depths is a premise. Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.Goal.Description.Live
import Johnson.Goal.Numbers.KeySeatLaidAt
import Johnson.Desc.Laid.ProofFullScope
import Johnson.Flat.Dec.FitAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Flat OnBytes.Slice OnBytes.Maker
open LPFD.Full (XF KF)
open Johnson.G (writtenKFull writtenPFull blocks_keyFull blocks_proofFull workFit_keyFull
  depthFit_keyFull workFit_proofFull depthFit_proofFull cntFrameFull_written entryFitB_dsFull)

/-- The number of blocks at the written data. -/
theorem kf_written : KF writtenKFull writtenPFull = 24086 := by
  have h0 := kMax_frRds_le
  unfold KF PV.Front.KFull kThree
  rw [blocks_keyFull, blocks_proofFull, OnBytes.Slice.fr_ds_C]
  apply le_antisymm
  · exact max_le (max_le (by norm_num) (max_le (h0.trans (by norm_num)) le_rfl)) (by norm_num)
  · exact le_max_of_le_left (le_max_of_le_right (le_max_right _ _))

/-- None of the six written lists of rounds is empty. -/
theorem listsFull_written : listsFull writtenKFull writtenPFull = true := by
  have k := Johnson.G.len_keyFull
  have p := Johnson.G.len_proofFull
  rw [Johnson.G.lenE_eq, Johnson.G.lenE_eq, Johnson.G.lenE_eq] at k p
  rw [Johnson.G.writtenKFull_eq, Johnson.G.writtenPFull_eq]
  unfold listsFull
  rw [show Johnson.G.dKeyFull.ds₁.length = 18850 by omega,
    show Johnson.G.dKeyFull.ds₂.length = 68 by omega,
    show Johnson.G.dKeyFull.ds₃.length = 30 by omega,
    show Johnson.G.dProofFull.ds₁.length = 48292 by omega,
    show Johnson.G.dProofFull.ds₂.length = 68 by omega,
    show Johnson.G.dProofFull.ds₃.length = 30 by omega]
  rfl

/-- **The four tests accept at the written data.** -/
theorem liveOf_written (G : FilesParameters XF RecFull)
    (hd : G.c.first.binding.logLeaves + G.k.oneTime.binding.logLeaves ≤ 332598) :
    dataWellFormedAtFullSizeDepth G writtenKFull writtenPFull = true := by
  have hk : kThree .two writtenKFull [] writtenPFull ≤ 24086 :=
    max_le (blocks_keyFull.le.trans (by norm_num)) (max_le (Nat.zero_le _) blocks_proofFull.le)
  have hc : cntFrameFullD writtenKFull writtenPFull dsFull frD.xs G.c.first.binding.logLeaves
      G.k.oneTime.binding.logLeaves ≤ theQueries := by
    rw [cntFrameFullD_landed, cntFrameFull_written]
    unfold theQueries
    omega
  have hl : sizeNumbersFitAtPlan KF theQueries G writtenKFull writtenPFull = true := by
    unfold sizeNumbersFitAtPlan sizeNumbersFitAtFullSize
    rw [kf_written]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨⟨⟨hk, entryFitB_dsFull⟩, workFit_keyFull⟩, depthFit_keyFull⟩, workFit_proofFull⟩,
      depthFit_proofFull⟩, hc⟩, by norm_num⟩
  have ha : (32 == frS.P.T.a) = true := by rw [Johnson.G.fr_a]; rfl
  unfold dataWellFormedAtFullSizeDepth dataWellFormedApartFromDepth
  rw [hl, listsFull_written]
  show ((32 == frS.P.T.a) && (32 == frS.P.T.a) && (true && true)) = true
  rw [ha]
  rfl

/-- **In scope: three returns and a bound on two depths give that `protocolDataWellFormed` accepts.** -/
theorem theLive_of_returns (Z : VerifierAndGoals.PublicFiles) (hZ : VerifierAndGoals.InScope Z = true) {G : FilesParameters XF RecFull}
    {K : WholeD × (RecFull → _root_.Run.PQ.View → _root_.Run.PQ.View → _root_.Run.PQ.View → Bool)}
    {P : WholeD ×
      (XF × RecFull → _root_.Run.PQ.View → _root_.Run.PQ.View → _root_.Run.PQ.View → Bool)}
    (hG : thePlanLaid (VerifierAndGoals.asDescriptionFiles Z) = .ok G) (hK : theKeyLaid (VerifierAndGoals.asDescriptionFiles Z) = .ok K)
    (hP : theProofLaid (VerifierAndGoals.asDescriptionFiles Z) = .ok P)
    (hd : G.c.first.binding.logLeaves + G.k.oneTime.binding.logLeaves ≤ 332598) :
    protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true := by
  have eK : K.1 = writtenKFull :=
    VerifiableInference.PlanWritten.laid_data_written (o := OnBytes.secondHashFunction) (r := K.2) hZ hK
  have eP : P.1 = writtenPFull :=
    LPFD.Full.laidPOf_written (o := OnBytes.secondHashFunction) (r := P.2) hZ hP
  have hG' : filesParametersOrRefusalAt OnBytes.secondHashFunction (VerifierAndGoals.asDescriptionFiles Z) = .ok G := hG
  have hK' : keyDataAndDecisionOrRefusalAt OnBytes.secondHashFunction (VerifierAndGoals.asDescriptionFiles Z) = .ok K := hK
  have hP' : proofDataAndDecisionOrRefusalAt OnBytes.secondHashFunction (VerifierAndGoals.asDescriptionFiles Z) = .ok P := hP
  unfold protocolDataWellFormed protocolDataWellFormedAt
  rw [hG', hK', hP']
  show dataWellFormedAtFullSizeDepth G K.1 P.1 = true
  rw [eK, eP]
  exact liveOf_written G hd

end FlashProve

#print axioms FlashProve.kf_written
#print axioms FlashProve.listsFull_written
#print axioms FlashProve.liveOf_written
#print axioms FlashProve.theLive_of_returns
