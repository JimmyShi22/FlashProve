-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K11/MaskLotCoveredAtZero.lean: `k11MaskLot_covered` (MaskLotCovered.lean of this folder)
ON CHAIN 0, WITH ONE OF ITS TWO PREMISES ON THE SENDER PAID: hh, that the frame hands the switch its
stretches at every run's coins: by `handed_at_book` (AtFullSide/K2/HandedAtTheBook.lean). ONE
PREMISE ON THE SENDER IS LEFT, BY NAME: hv: at every valid input the switch's public test `publicOk`
says yes at the input's public instance. One lemma: a call; no definition; nothing is evaluated
here; none of the library's goals. It lies in the side library because it imports files of it.

WHAT IT IS NOT. hv IS PAID BY NOBODY. All that MaskLotCovered.lean says under "WHAT IT IS NOT"
stands: no list is laid and no Script; that a thread's book is what bookWhole returns at F0T is not
said. Chain 0 alone. Of the kind's own lot at that book another file of this folder,
LotsAnswerAtTheBook.lean, which is not imported here, says: it answers at its entries on chain 0,
and nowhere on chain 1; of a chain's number from 2 on nobody has asked.

Limits. Closed facts by Lean's kernel lie beneath. The full size; the format's second hash function. All
limits of MaskLotCovered.lean and HandedAtTheBook.lean stand. Nothing on any property.
-/
import AtFullSide.K11.MaskLotCovered
import AtFullSide.K2.HandedAtTheBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open Johnson.G (proofSendsFull)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.FirstThread (MsgLot Covers)
open ProofFile.Honest.K11 (k11MaskLot)
open ProofFile.Honest.K2 (SwitchPlace switchPlaces switchMsgTxt lotClosingAt segmentsOf publicOk
  switchNum)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {B : ProverCoinCounts}

/-- THE HEAD, THE OPENING, THE BASE, THE BOOK AND hv ARE PREMISES. **ON CHAIN 0 THE KIND's FIRST LOT
IS COVERED BY ITS SENDER's WHOLE-MESSAGE LOT, UNDER hv ALONE OF THE TWO PREMISES ON THE SENDER.** -/
theorem k11MaskLot_covered_at_zero {W₀ Rc Tr : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hb : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (X : Type) (claims : ProofFile.Inst → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights) (Dr : RowDataOf ProofFile.Inst)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (lay : OnBytes.Params.ReqLayout)
    {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) (hl : p.link = 24)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (N fx : Nat)
    (hv : ∀ w, Vd w → publicOk Dr lay p ((segmentsOf Zp Bs.G₀).take p.link) w.x = true) :
    Covers Vd N
      (⟨switchNum Zp p 2, fx,
        switchMsgTxt 0 Dr readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p 2⟩ :
          MsgLot B (Local W₀ Rc ProofFile.Inst Tr))
      (k11MaskLot B (Rc := Rc) (Tr := Tr) X 0 IM.k11Place (_root_.K11.parOf Zp Bs.G₀) claims
        weights (P5J.At.num Zp 24 0) 3531) :=
  k11MaskLot_covered h O hb hB X 0 claims weights Dr readers lay hp hl Vd N fx
    (fun k => AtFullSide.K2.handed_at_book h O hB hp k) hv

end AtFullSide.K11

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K11.k11MaskLot_covered_at_zero
