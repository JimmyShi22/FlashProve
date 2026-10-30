-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/Part4/DepthsAtW.lean: THE LAST CHAIN's PROXIMITY TEST (the kind K12, the place W):
THE THREE TAKEN TREES' DEPTHS (TakenDepths, K12/AtFile/WDepths.lean, of other authors) AT THE BASE
PROVER's OWN TABLES: the first chain's Script's table at its own trees 1 and 82 has depth 13 and 22,
and the shared chain's tableShared at its own tree 1 has depth 22, AT ALL COINS, INPUTS AND LISTS OF
CHALLENGES, under the library's hypothesis on the first chain and the maker's return.

WHAT IT IS NOT.
  * Depths (the field logLength) alone: nothing on what a table holds.
  * The hypothesis (P5J.AtMgA: the full size and the format's second hash function alone) and hA, that the
    maker returns A at the filling onlineProverPartsInUse, are premises.
  * AT THE FILLING, NOT READ THROUGH: at the base prover's filling's return; not at the online
    prover.
  * "At all coins" rests on the book: where a book did not cover a sender's count, that sender's
    table would be the table without a word, of another depth. Here the book is the one made of the
    written description (bookOfTheReturn), which covers the three.
  * In the side library.
  * Nothing on completeness, soundness or what a proof hides.

WHAT IT IS. No definition; three theorems.

  depthsOfTheSendersTables   at the maker's written book, the tables of tree 1 of a sending at the
                             first written plan and of tree 0 of one at W's written plan have depths
                             13 and 22, at all arguments
  depthOfTheSharedTable      tableShared at own 1 has depth 22, at all arguments
  depthsAtW                  **TakenDepths**, at every r₁ and toCommon

CALLED. armsAtTheFirstScript (ArmsAtTheFirstScript.lean); bookOfTheReturn
(TakenAtTheBaseProver.lean); bookCoversTheSenders (BookCoversTheSenders.lean); sendingsAtTheHead
(JobAtTheHead.lean). Of other authors: treeTbl_depth, cols_written
(AtFullSide/K12/FirstArmsK1.lean); omega_depth_head (K12/AtFile/WJointBook.lean); treesU_head
(K12/AtFile/TreesAtShared.lean). The step that reads tableShared's arm at own 1 is that of
omega_arm_head (K12/AtFile/WJointFour.lean), walked anew here: that file is not beneath this one.
-/
import AtFullSide.K12.Part4.TakenAtTheBaseProver
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WDepths
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TreesAtShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12.Part4
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Part4
open OnBytes (TableKey)
open VerifiableInference.Desc (Chain K1.qAt)
open VerifiableInference.Desc.K1 (parGF parWF)
open ProofFile.Honest.K12.AtFile (TakenDepths tableShared treesU_head omega_depth_head)
open ProofFile.Honest.K1 (LocB firstScriptAt)
open ProofFile.Honest.K14 (jobOmega sendTable sendPlace witOf treesU)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open P5J (TS)

/-- **At the maker's written book the two senders' tables have depths 13 and 22**, at all coins,
inputs and lists of challenges. sentI, sentW: sendings' jobs at the written plans and rides. -/
theorem depthsOfTheSendersTables {Bk : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk) {W WS XS : Type} (sentI sentW : K1.SendJob WS XS)
    (planI : sentI.P = parGF) (rideI : sentI.ride = writtenRideOfTheIndexMasks)
    (planW : sentW.P = parWF) (rideW : sentW.ride = writtenRideOfW) (witness : W → WS) (own₀ : XS)
    (k : Coins Bk) (w : W) (hd : List Fmt.Drawn) :
    (K1.treeTbl 0 witness sentI own₀ 1 k w hd).2.logLength = 13 ∧
      (K1.treeTbl 0 witness sentW own₀ 0 k w hd).2.logLength = 22 := by
  obtain ⟨PI, nI, rI, dI⟩ := sentI
  obtain ⟨PW, nW, rW, dW⟩ := sentW
  obtain rfl : PI = parGF := planI
  obtain rfl : rI = writtenRideOfTheIndexMasks := rideI
  obtain rfl : PW = parWF := planW
  obtain rfl : rW = writtenRideOfW := rideW
  obtain ⟨coverIndex, coverW⟩ := bookCoversTheSenders hB
  obtain ⟨cI, cutIndex⟩ := coverIndex k
  obtain ⟨cW, cutW⟩ := coverW k
  obtain ⟨-, -, -, -, treesI, treesW, depthI, depthW⟩ := cols_written
  exact ⟨(treeTbl_depth 0 witness ⟨parGF, nI, writtenRideOfTheIndexMasks, dI⟩ own₀ 1 k w hd cutIndex
      treesI).trans depthI,
    (treeTbl_depth 0 witness ⟨parWF, nW, writtenRideOfW, dW⟩ own₀ 0 k w hd cutW treesW).trans
      depthW⟩

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **The shared chain's table at its own tree 1 has depth 22**, at all arguments. Premises: the
hypothesis and that the book is the one made of the written description. -/
theorem depthOfTheSharedTable {Bk : ProverCoinCounts} (h : P5J.AtMg OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF)
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk) {Ws Rs Xs : Type} (weights : Ws → Weights)
    (rand : Rs → TableRand) (testOnU testOnOmega : TestJob (Common Ws Rs TableKey) Xs)
    (ownShared : Xs) (k : Coins Bk) (v : Common Ws Rs TableKey) (hd : List Fmt.Drawn) :
    (tableShared (K1.qAt Zp Np) weights rand testOnU testOnOmega ownShared (.own 1) k v
      hd).2.logLength = 22 := by
  have one := treesU_head h
  have arm : tableShared (Bk := Bk) (K1.qAt Zp Np) weights rand testOnU testOnOmega ownShared
      (.own 1) =
      sendTable (jobOmega ⟨K1.qAt Zp Np, 0⟩) (witOf (K1.qAt Zp Np) weights rand) (sendPlace 5) 1
        0 := by
    show (if 1 < treesU (K1.qAt Zp Np) then _ else if 1 < 3 then _ else _) = _
    rw [if_neg (by omega), if_pos (by omega), one]
  rw [arm]
  exact omega_depth_head h hB (An := ⟨K1.qAt Zp Np, 0⟩) rfl _ k v hd

/-- **TakenDepths at the base prover's own tables**: the first chain's Script's table and the shared
chain's tableShared; at every r₁ and toCommon. -/
theorem depthsAtW {W₀ : Type} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {x : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    {Ws Rs Xs : Type} (weights : Ws → Weights) (rand : Rs → TableRand)
    (testOnU testOnOmega : TestJob (Common Ws Rs TableKey) Xs) (ownShared : Xs) (r₁ : ℕ)
    (toCommon : LocB W₀ → Common Ws Rs TableKey) :
    TakenDepths r₁ toCommon (firstScriptAt I S Op A cF).table
      (tableShared (K1.qAt A.Z Np) weights rand testOnU testOnOmega ownShared) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hB := bookOfTheReturn h hA
  have both : ∀ k v hd, ((firstScriptAt I S Op A cF).table (.own 1) k v hd).2.logLength = 13 ∧
      ((firstScriptAt I S Op A cF).table (.own 82) k v hd).2.logLength = 22 := by
    intro k v hd
    obtain ⟨tableIndex, tableW, -⟩ := armsAtTheFirstScript h O hA (fun _ _ => none)
      (fun _ _ _ _ => True) 0 0 0 0 (fun _ => True) (fun _ _ _ => True) (fun _ _ _ => True) v
    obtain ⟨planI, rideI, planW, rideW⟩ := sendingsAtTheHead (X := Unit) h O S
      (K1.lotNo OnBytes.secondHashFunction A.Z ⟨1, none, 4, .K1⟩) (K13.wDataAt Op.pile A.Z Bs.G₀)
    have depths := depthsOfTheSendersTables hB
      (K1.placeJob (X := Unit) (VerifiableInference.Desc.K1.firstPar Bs.G₀.first
        (VerifiableInference.Desc.K1.gpOf A.Z)) (K1.lotNo OnBytes.secondHashFunction A.Z ⟨1, some 0, 1, .K1⟩)
        (K1.firstFold Bs.G₀.first) (K1.lotData S A.Z Bs.G₀))
      (K1.wJobAt (X := Unit) A.Z.first (K1.wGp A.Z) 4 VerifiableInference.Desc.K13.Law.wMsgFull
        (K1.lotNo OnBytes.secondHashFunction A.Z ⟨1, none, 4, .K1⟩) (K13.wDataAt Op.pile A.Z Bs.G₀))
      planI rideI planW rideW (ProofFile.Honest.K12.AtProof.inOf (K1.readersB I A.Z)) () k v hd
    exact ⟨(congrArg (·.2.logLength) (tableIndex k v hd)).trans depths.1,
      (congrArg (·.2.logLength) (tableW k v hd)).trans depths.2⟩
  exact ⟨fun k v hd => (both k v hd).1, fun k v hd => (both k v hd).2,
    fun k v hd => depthOfTheSharedTable h.toAtMg hB weights rand testOnU testOnOmega ownShared k v
      hd⟩

end AtFullSide.K12.Part4

#print axioms AtFullSide.K12.Part4.depthsOfTheSendersTables
#print axioms AtFullSide.K12.Part4.depthOfTheSharedTable
#print axioms AtFullSide.K12.Part4.depthsAtW
