-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K11/IndexLotCovered.lean: THE KIND K11's SECOND LOT OF ENTRIES (`k11IndexLot`: one entry
of the index masks' message) IS COVERED, IN THE FORM `Covers`
(Johnson/Desc/ProofFile/Honest/Small/Covers.lean, another group of authors'), BY A WHOLE-MESSAGE LOT
OF ITS SENDER: THE OPENING's SENDER OF THE KIND K1, MESSAGE 4 (`msgTxt`, Honest/K1/ScriptLots.lean,
a third group's): UNDER THE LIBRARY's HEAD AND THE OPENING, AT WHATEVER BOOK bookWhole RETURNS AT
F0T, ON CHAIN 0, AT A JOB WITH THE OPENING's NUMBERS AND RIDES. NO PREMISE ON WHETHER THE SENDER
ANSWERS IS LEFT: that is one public test on the book (`K1.bookCovers`), had at that book
(`opening_covers_at_book`, OpeningCoversAtTheBook.lean of this folder). No definition. Two lemmas;
none of the library's goals. It lies in the side library because it imports files of it.

  `k11IndexLot_covered`
      THE LAW: `Covers Vd N` (the sender's lot) (the kind's lot), at every Vd, N and fx
  `k11IndexLot_ownMsgs`
      so `OwnMsgs` at the kind's lot at `Script.ofLots`: by `ofLots_ownMsgs_of_covers`

How. The numbers are one letter on both sides. Where the kind's text answers y: the book covers the
sender's count, so the sender's cut is there (`K1.lentCut_isSome`) and its text answers at every
entry (`K1.msgTxt_some`); and the two answers are one (`indexLot_agrees_at_book`, AtTheBook.lean of
this folder).

WHAT IT IS NOT. THE SENDER's LOT BEARS THE NUMBER `k4IndexNum Zp` AS WRITTEN: that the lot which
K1's list `k1MsgLots` lays for message 4 is this very lot, where the list is numbered by
`P5J.At.arr Zp` and holds the opening's job at member 2, is not said here: it is `openingLot_mem`
(Honest/K11/Plays/IndexLotInList.lean). J IS A LETTER, tied by its numbers and rides alone: its
data, and wit and own₀, are free. NO LIST IS LAID AND NO SCRIPT: that the sender's lot lies in a
list, and that the other lots of its message agree with it, are premises of the last lemma; it leans
on the frame's authors' rule that senders' whole-message lots alone are laid. THE BOOK IS WHAT
bookWhole RETURNS AT F0T: that a thread's book is that one is not said. COVERS, NOT LENDS: whether
the frame lends the sender's part is another question. Nothing on what a coin is worth or how it is
drawn.

Limits. Nothing is evaluated here; closed facts by Lean's kernel lie beneath, four of them in
OpeningCoversAtTheBook.lean. CHAIN 0 ALONE: the sister file on the first lot (MaskLotCovered.lean)
has the chain's number as a letter: whoever calls both lays 0 there. The full size; the format's
second hash function. All limits of AtTheBook.lean and OpeningCoversAtTheBook.lean stand. Nothing on any
property.
-/
import AtFullSide.K11.AtTheBook
import AtFullSide.K11.OpeningCoversAtTheBook
import Johnson.Desc.ProofFile.Honest.K1.ScriptLots
import Johnson.Desc.ProofFile.Honest.Small.Covers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.FillP1 (fvsAt)
open VerifiableInference.Desc.K1 (parGF qFull firstPar gpOf)
open Johnson.Desc.First.Walk.Tied (rowsBefore)
open Johnson.G (proofSendsFull)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.FirstThread (MsgLot PadLot TreeLot Covers OwnMsgs LotsAgree
  ofLots_ownMsgs_of_covers)
open ProofFile.Honest.K1 (SendJob msgTxt)
open ProofFile.Honest.K4.Lot (k4IndexRows k4IndexNum)
open ProofFile.Honest.K11 (k11IndexLot)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {B : ProverCoinCounts}

/-- THE HEAD, THE OPENING, THE BOOK, hP AND hR ARE PREMISES. **THE KIND's SECOND LOT IS COVERED BY
ITS SENDER's WHOLE-MESSAGE LOT.** -/
theorem k11IndexLot_covered {W₀ Rc Tr W Y : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (X : Type) (claims : ProofFile.Inst → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (wit : Local W₀ Rc ProofFile.Inst Tr → W) (J : SendJob W Y) (own₀ : Y)
    (hP : J.P = firstPar Bs.G₀.first (gpOf Zp))
    (hR : J.ride = K1.rideOf (K1.firstFold Bs.G₀.first))
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (N fx : Nat) :
    Covers Vd N (⟨k4IndexNum Zp, fx, msgTxt 0 wit J own₀ 4⟩ : MsgLot B (Local W₀ Rc ProofFile.Inst Tr))
      (k11IndexLot B (Rc := Rc) (Tr := Tr) X 0 IM.k11Place (_root_.K11.parOf Zp Bs.G₀) claims
        weights (k4IndexNum Zp) (rowsBefore (fvsAt Zp) 24 % k4IndexRows Zp)
        (rowsBefore (fvsAt Zp) 24 / k4IndexRows Zp)) := by
  refine ⟨rfl, ?_⟩
  intro k w hd _ _ mask row place y h1
  have hs : (K1.lentCut k 0 ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride)).isSome = true := by
    rw [K1.lentCut_isSome k 0 (by omega), hP, hR]
    exact opening_covers_at_book h O hB
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hs
  have h2 := K1.msgTxt_some 0 wit J own₀ 4 k c hc w (hd.take fx) mask row place
  have e := indexLot_agrees_at_book h O hB W₀ Rc Tr X 0 claims weights W Y wit J own₀ hP hR k w _ _
    mask row place y _ h1 h2
  show msgTxt 0 wit J own₀ 4 k w (hd.take fx) mask row place = some y
  rw [h2, e]

/-- **So a Script laid of a list in which the sender's lot lies, the other lots of its message
agreeing with it, has `OwnMsgs` at the kind's lot.** -/
theorem k11IndexLot_ownMsgs {W₀ Rc Tr W Y St Cl Cells Tok : Type}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (X : Type) (claims : ProofFile.Inst → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (wit : Local W₀ Rc ProofFile.Inst Tr → W) (J : SendJob W Y) (own₀ : Y)
    (hP : J.P = firstPar Bs.G₀.first (gpOf Zp))
    (hR : J.ride = K1.rideOf (K1.firstFold Bs.G₀.first))
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (N fx : Nat)
    (bs : List (Block St Cl)) (front : Nat) (cells : Local W₀ Rc ProofFile.Inst Tr → Cells)
    (tok : Local W₀ Rc ProofFile.Inst Tr → Tok) (pl : List (PadLot B (Local W₀ Rc ProofFile.Inst Tr)))
    (tl : Nat → TreeLot B (Local W₀ Rc ProofFile.Inst Tr))
    (ml : List (MsgLot B (Local W₀ Rc ProofFile.Inst Tr)))
    (hin : (⟨k4IndexNum Zp, fx, msgTxt 0 wit J own₀ 4⟩ :
      MsgLot B (Local W₀ Rc ProofFile.Inst Tr)) ∈ ml)
    (hag : LotsAgree ml (⟨k4IndexNum Zp, fx, msgTxt 0 wit J own₀ 4⟩ :
      MsgLot B (Local W₀ Rc ProofFile.Inst Tr))) :
    OwnMsgs (FirstThread.Script.ofLots bs front cells tok pl tl ml) Vd N (k4IndexNum Zp) 0
      (k11IndexLot B (Rc := Rc) (Tr := Tr) X 0 IM.k11Place (_root_.K11.parOf Zp Bs.G₀) claims
        weights (k4IndexNum Zp) (rowsBefore (fvsAt Zp) 24 % k4IndexRows Zp)
        (rowsBefore (fvsAt Zp) 24 / k4IndexRows Zp)).txt :=
  ofLots_ownMsgs_of_covers bs front cells tok pl tl ml hin hag
    (k11IndexLot_covered h O hB X claims weights wit J own₀ hP hR Vd N fx)

end AtFullSide.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K11.k11IndexLot_covered
#print axioms AtFullSide.K11.k11IndexLot_ownMsgs
