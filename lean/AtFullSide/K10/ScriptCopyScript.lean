-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/ScriptCopyScript.lean: the base prover's Script of the first chain (`firstScriptAt`, AtFullSide/K1/FirstScript.lean) and three facts on it, in
the letters in which the law on a code switch's messages at the joined Script is stated (`msgs_at_lot_data`,
AtFullSide/K2/MsgsAtLotData.lean, which this file does not import): the list of the shared kind's jobs by `byNo` at the opening's
ground, and the code switch's share at `withSwitchData S (K1.lotData S)` at that ground.

  `script_is_joinQ`   the Script is `joinQ` at that list
  `switchShare_open`, `testShare_open`   the two shares of the other senders' record, at the opening's ground
  `fit_at_byNo`       the joined list of all three senders is fit, at that list
  `share_in_byNo`     the code switch's share lies in the other senders' record
  `witB_x`, `witB_R`   the shared kind's reader hands the input's own instance, and the readers that the switches read

By `byNo_at_head` (Johnson/Desc/ProofFile/Honest/Thread/JoinAtHead.lean), `joinFit_full` (AtFullSide/K2/JoinFitFull.lean),
`otherSenders_at_head`, `switch_in_first`, `testJob_six` (FirstScript.lean), `atPure_at_laid_ground`.

Limits. The hypothesis on the head, the opening and the maker's return are premises. Equations and public tests on a Script: what is
written where. The full size and the older hash alone.
-/
import AtFullSide.K1.FirstScript

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open VerifiableInference.Desc (Chain Block)
open OnBytes.Maker (WholeD)
open OnBytes.SendSim.Seat (wJobs)
open P5J (AtMgA TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.FirstThread (joinQ JoinFit byNo byNo_at_head)
open ProofFile.Honest.K1 (firstScriptAt otherSendersAt switchShareB testShareOf testJobAt testOk shapeAtSeat cellsB tokB witB
  readersB noTree LocB lotNo jobTwoAt jobLaterAt jobWAt k1MembersW otherSenders_at_head switch_in_first testJob_six)
open ProofFile.Honest.K2 (switchShareAt withSwitchData)

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- **The Script is `joinQ` at the list of the shared kind's jobs by their own places' numbers, at the opening's
ground.** -/
theorem script_is_joinQ (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction A.Z Np cF) A.Z Bs base cF
      (seatZ A.Z Np) (secondAt A.Z Np))
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A) :
    firstScriptAt I S Op A cF =
      joinQ cF.blocksInOrder 0 (cellsB I A.Z) tokB (P5J.At.arr A.Z) (witB I A.Z) ()
        (byNo cF.blocksInOrder (K1.lotJobs (X := Unit) (lotNo OnBytes.secondHashFunction A.Z) (K1.lotData S) A.Z Bs.G₀ ++
                   wJobs (X := Unit) (lotNo OnBytes.secondHashFunction A.Z) (K13.wDataAt Op.pile) A.Z Bs.G₀))
        (otherSendersAt I S A cF) := by
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have key : byNo cF.blocksInOrder
      (K1.lotJobs (X := Unit) (lotNo OnBytes.secondHashFunction A.Z) (K1.lotData S) A.Z Bs.G₀ ++
        wJobs (X := Unit) (lotNo OnBytes.secondHashFunction A.Z) (K13.wDataAt Op.pile) A.Z Bs.G₀) =
      k1MembersW (jobTwoAt S A.Z A.G) (jobLaterAt S A.Z A.G) (jobWAt Op A.Z A.G) := by
    rw [eG]
    exact byNo_at_head h O (lotNo OnBytes.secondHashFunction A.Z) (K1.lotData S) (K13.wDataAt Op.pile)
  exact (congrArg (fun js => joinQ cF.blocksInOrder 0 (cellsB I A.Z) tokB (P5J.At.arr A.Z)
    (witB I A.Z) () js (otherSendersAt I S A cF)) key).symm

/-- The code switch's share, at the opening's ground. -/
theorem switchShare_open (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction A.Z Np cF) A.Z Bs base cF
      (seatZ A.Z Np) (secondAt A.Z Np))
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A) :
    switchShareB I S A cF =
      switchShareAt A.B cF.blocksInOrder 0 A.Z Bs.G₀ (withSwitchData S (K1.lotData S) A.Z Bs.G₀) (readersB I A.Z)
        noTree := by
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  show switchShareAt A.B cF.blocksInOrder 0 A.Z A.G (withSwitchData S (K1.lotData S) A.Z A.G) (readersB I A.Z)
    noTree = _
  rw [eG]

/-- The proximity test's share at a finish, at the opening's ground. -/
theorem testShare_open (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction A.Z Np cF) A.Z Bs base cF
      (seatZ A.Z Np) (secondAt A.Z Np))
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    (pl : K2.SwitchPlace) :
    testShareOf I S A cF pl =
      K12.k12Share 0 (testJobAt I S A.Z Bs.G₀ pl) () (roundsTo cF.blocksInOrder 354) 77 (P5J.At.arr A.Z)
        testOk pl.sizes.codes (fun τ => shapeAtSeat A.Z (77 + τ) 0)
        (fun τ => shapeAtSeat A.Z (77 + τ) 1) 354 noTree := by
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  show K12.k12Share 0 (testJobAt I S A.Z A.G pl) () (roundsTo cF.blocksInOrder 354) 77 (P5J.At.arr A.Z)
    testOk pl.sizes.codes (fun τ => shapeAtSeat A.Z (77 + τ) 0)
    (fun τ => shapeAtSeat A.Z (77 + τ) 1) 354 noTree = _
  rw [eG]

/-- **The joined list of all three senders is fit**, at that list. -/
theorem fit_at_byNo (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction A.Z Np cF) A.Z Bs base cF
      (seatZ A.Z Np) (secondAt A.Z Np))
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A) :
    JoinFit cF.blocksInOrder 0 (P5J.At.arr A.Z) (P5J.At.seats A.Z) (witB I A.Z) ()
      (byNo cF.blocksInOrder (K1.lotJobs (X := Unit) (lotNo OnBytes.secondHashFunction A.Z) (K1.lotData S) A.Z Bs.G₀ ++
                 wJobs (X := Unit) (lotNo OnBytes.secondHashFunction A.Z) (K13.wDataAt Op.pile) A.Z Bs.G₀))
      (otherSendersAt I S A cF) := by
  obtain ⟨pl, -, e⟩ := otherSenders_at_head (I := I) (S := S) h hA
  rw [e, switchShare_open h O hA, testShare_open h O hA pl]
  exact K2.Law.joinFit_full h O hA (lotNo OnBytes.secondHashFunction A.Z) (K1.lotData S)
    (K13.wDataAt Op.pile) 0 (witB I A.Z) () (withSwitchData S (K1.lotData S) A.Z Bs.G₀) (readersB I A.Z)
    noTree 0 (testJobAt I S A.Z Bs.G₀ pl) (testJob_six (I := I) (S := S) h pl) ()
    (roundsTo cF.blocksInOrder 354) testOk pl.sizes.codes (fun τ => shapeAtSeat A.Z (77 + τ) 0)
    (fun τ => shapeAtSeat A.Z (77 + τ) 1) noTree

/-- **The code switch's share lies in the other senders' record.** -/
theorem share_in_byNo (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction A.Z Np cF) A.Z Bs base cF
      (seatZ A.Z Np) (secondAt A.Z Np))
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A) :
    K2.Law.ShareIn
      (switchShareAt A.B cF.blocksInOrder 0 A.Z Bs.G₀ (withSwitchData S (K1.lotData S) A.Z Bs.G₀) (readersB I A.Z)
        noTree) (otherSendersAt I S A cF) := by
  rw [← switchShare_open h O hA]
  exact switch_in_first

/-- The shared kind's reader hands the input's own instance. -/
theorem witB_x (I : WiderIn W₀) (Zq : ProofFile.Pub) (w : LocB W₀) : (witB I Zq w).x = w.x := rfl

/-- And the readers that the switches read. -/
theorem witB_R (I : WiderIn W₀) (Zq : ProofFile.Pub) (w : LocB W₀) : (witB I Zq w).R = readersB I Zq w := rfl

end AtFullSide.K10

#print axioms AtFullSide.K10.script_is_joinQ
#print axioms AtFullSide.K10.switchShare_open
#print axioms AtFullSide.K10.testShare_open
#print axioms AtFullSide.K10.fit_at_byNo
#print axioms AtFullSide.K10.share_in_byNo
#print axioms AtFullSide.K10.witB_x
#print axioms AtFullSide.K10.witB_R
