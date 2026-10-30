-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K11/MaskLotCovered.lean: THE KIND K11's FIRST LOT OF ENTRIES (`k11MaskLot`: 2 lk + 2
entries of mask row 0 of the segment's mask message) IS COVERED, IN THE FORM `Covers`
(Johnson/Desc/ProofFile/Honest/Small/Covers.lean), BY ITS SENDER's
WHOLE-MESSAGE LOT: THE SWITCH INTO LINK 24, MESSAGE 2 (`switchMsgTxt`, Honest/K2/ScriptLots.lean):
UNDER THE LIBRARY's HEAD AND THE OPENING, AT WHATEVER BOOK bookWhole RETURNS AT F0T, AND UNDER TWO
PREMISES ON THE SENDER, BY NAME. So, where that sender's lot lies in the list and the other lots of
its message agree with it, a Script laid of the list has `OwnMsgs` at the kind's lot. One
definition: a public test. Lemmas; none of the library's goals. It lies in the side library because
it imports files of it.

  `link24Own` kept p
      A PUBLIC TEST: at link 24 the switch keeps so many earlier messages, sends at least one own
      message of the next segment, its sending has a message 2, and `firstSender` lets 2 by
  `link24OwnW`, `link24OwnW_can_fail`
      BY LEAN's KERNEL, at the written places: yes at all · a control: with two kept in the stead
      of one it says no at some place
  `link24Own_at_head`
      the test's yes at every place of the plan
  `switchNum_at_24`
      THE NUMBER: `switchNum Zp p 2 = P5J.At.num Zp 24 0` at the place of link 24: by
      `ownNums_at_head` (Honest/K2/Law/OwnRolesAtHead.lean)
  `senderLot_mem`
      the sender's lot, as it is written here, IS A MEMBER OF K2's OWN LIST `switchMsgLots` at that
      switch, at the numbering `switchNum Zp p`: so the last lemma's premise hin can be met there
  `k11MaskLot_covered`
      THE LAW: `Covers Vd N` (the sender's lot) (the kind's lot)
  `k11MaskLot_ownMsgs`
      so `OwnMsgs` at the kind's lot at `Script.ofLots`: by `ofLots_ownMsgs_of_covers` (theirs)

THE TWO PREMISES ON THE SENDER, PAID BY NOBODY HERE. hh: at every run's coins the frame hands the
switch's part its stretches (`handed`). hv: at every valid input the switch's public test `publicOk`
says yes at the input's public instance. They are the two to which K2's authors have brought the
question whether `switchMsgTxt` answers (`msgTxt_answers_two`, Honest/K2/Law/LotsAnswerAtHead.lean).
BOTH ARE ASKED AT MORE THAN IS SPENT: hh at every k, hv at every valid input: the proof calls them
only at a k and an input at which the kind's own text answers.

How. The number. Then, where the kind's text answers y: the sender's answers some y'
(`msgTxt_answers_two`); and y' = y (`maskLot_agrees_at_book`, AtTheBook.lean of this folder: one
public test on the book's entries, had at that book).

WHAT IT IS NOT. NO LIST IS LAID AND NO SCRIPT: that the sender's lot lies in the list ml, and that
the other lots of its message in ml agree with it (hag), are premises of the last lemma. hag speaks
of each member of ml with the sender's number: this file counts on the frame's authors' plan that
senders' whole-message lots alone are laid into ml: a list that held the kind's own lot as well
would owe `maskLot_agrees` a second time, inside hag. On chain: ch is a letter here; the sister file
on the second lot (IndexLotCovered.lean) stands at chain 0 alone: whoever calls both takes ch := 0.
THE BOOK IS WHAT bookWhole RETURNS AT F0T: that a thread's book is that one is not said. fx, the
sender's lot's number of challenges, is a letter. The kind's second lot (`k11IndexLot`) is not
treated. Nothing on what a coin is worth or how it is drawn.

Limits. TWO CLOSED FACTS BY EVALUATION IN LEAN's KERNEL, one a control; more lie beneath. The full
size; the format's second hash function. All limits of AtTheBook.lean stand. Nothing on any property.
-/
import AtFullSide.K11.AtTheBook
import Johnson.Desc.ProofFile.Honest.K2.Law.LotsAnswerAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.OwnRolesAtHead
import Johnson.Desc.ProofFile.Honest.Small.Covers

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
open ProofFile.Honest.FirstThread (MsgLot PadLot TreeLot Covers OwnMsgs LotsAgree
  ofLots_ownMsgs_of_covers)
open ProofFile.Honest.K11 (k11MaskLot)
open ProofFile.Honest.K2 (SwitchPlace switchPlaces switchMsgTxt lotClosingAt segmentsOf handed publicOk
  switchNum switchSent firstSender switchMsgLots Closing)
open ProofFile.Honest.K2.Law (placesW places_at_head ownNums_at_head msgTxt_answers_two)

/-- **A PUBLIC TEST**: at link 24 one earlier message is kept, at least one own message of the next
segment is sent, message 2 is a message of the sending, and the switch is its first sender. kept:
1; a control lays 2. -/
def link24Own (kept : Nat) (p : SwitchPlace) : Bool :=
  p.link != 24 || (p.sizes.kept.length == kept && decide (0 < p.others.size - 1) &&
    decide (2 < (switchSent p.sizes p.others).size) && firstSender p 2)

set_option maxRecDepth 1000000 in
/-- **At the written places.** -/
theorem link24OwnW : placesW.all (link24Own 1) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with two kept it says no at some place: so a place of link 24 stands in the list. -/
theorem link24OwnW_can_fail : placesW.all (link24Own 2) = false := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {B : ProverCoinCounts}

/-- The test's yes at every place of the plan. -/
theorem link24Own_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, link24Own 1 p = true := by
  intro p hp
  have hp' : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  exact List.all_eq_true.1 link24OwnW p hp'

/-- **THE NUMBER**: the switch into link 24 bears, for its message 2, the number of link 24's own
message 0. -/
theorem switchNum_at_24 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) (hl : p.link = 24) :
    switchNum Zp p 2 = P5J.At.num Zp 24 0 := by
  have t := link24Own_at_head h O p hp
  unfold link24Own at t
  rw [hl] at t
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at t
  have e := ownNums_at_head h.toAtMg O p hp 0 t.1.1.2
  rw [t.1.1.1, hl] at e
  exact e

/-- **THE SENDER's LOT IS A MEMBER OF K2's OWN LIST** at the switch into link 24, at the numbering
`switchNum Zp p`. -/
theorem senderLot_mem {W₀ Rc Xi Tr : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) (hl : p.link = 24)
    (ch : Nat) (Dr : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing)
    (fx : Nat) :
    (⟨switchNum Zp p 2, fx, switchMsgTxt ch Dr readers closing p 2⟩ :
        MsgLot B (Local W₀ Rc Xi Tr)) ∈
      switchMsgLots ch Dr readers closing p (switchNum Zp p) fx := by
  have t := link24Own_at_head h O p hp
  unfold link24Own at t
  rw [hl] at t
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at t
  unfold switchMsgLots
  exact List.mem_map.2 ⟨2, List.mem_filter.2 ⟨List.mem_range.2 t.1.2, t.2⟩, rfl⟩

/-- THE HEAD, THE OPENING, THE BASE, THE BOOK, hh AND hv ARE PREMISES. **THE KIND's FIRST LOT IS
COVERED BY ITS SENDER's WHOLE-MESSAGE LOT.** -/
theorem k11MaskLot_covered {W₀ Rc Tr : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hb : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (X : Type) (ch : Nat) (claims : ProofFile.Inst → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights) (Dr : RowDataOf ProofFile.Inst)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (lay : OnBytes.Params.ReqLayout)
    {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) (hl : p.link = 24)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (N fx : Nat)
    (hh : ∀ k : Coins B, (handed ch p k).isSome = true)
    (hv : ∀ w, Vd w → publicOk Dr lay p ((segmentsOf Zp Bs.G₀).take p.link) w.x = true) :
    Covers Vd N
      (⟨switchNum Zp p 2, fx,
        switchMsgTxt ch Dr readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p 2⟩ :
          MsgLot B (Local W₀ Rc ProofFile.Inst Tr))
      (k11MaskLot B (Rc := Rc) (Tr := Tr) X ch IM.k11Place (_root_.K11.parOf Zp Bs.G₀) claims
        weights (P5J.At.num Zp 24 0) 3531) := by
  refine ⟨switchNum_at_24 h O hp hl, ?_⟩
  intro k w hd hV _ mask row place y h1
  obtain ⟨y', h2⟩ := msgTxt_answers_two h.toAtMg O ch Dr readers lay hp 2 k w (hd.take fx) mask row
    place (hh k) (hv w hV)
  have e := maskLot_agrees_at_book h O hb hB X ch claims weights Dr readers lay hp hl k w _ _ mask
    row place y y' h1 h2
  show switchMsgTxt ch Dr readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p 2 k w (hd.take fx)
    mask row place = some y
  rw [h2, e]

/-- **So a Script laid of a list in which the sender's lot lies, the other lots of its message
agreeing with it, has `OwnMsgs` at the kind's lot.** -/
theorem k11MaskLot_ownMsgs {W₀ Rc Tr St Cl Cells Tok : Type}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hb : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (X : Type) (ch : Nat) (claims : ProofFile.Inst → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights) (Dr : RowDataOf ProofFile.Inst)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (lay : OnBytes.Params.ReqLayout)
    {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) (hl : p.link = 24)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (N fx : Nat)
    (hh : ∀ k : Coins B, (handed ch p k).isSome = true)
    (hv : ∀ w, Vd w → publicOk Dr lay p ((segmentsOf Zp Bs.G₀).take p.link) w.x = true)
    (bs : List (Block St Cl)) (front : Nat) (cells : Local W₀ Rc ProofFile.Inst Tr → Cells)
    (tok : Local W₀ Rc ProofFile.Inst Tr → Tok) (pl : List (PadLot B (Local W₀ Rc ProofFile.Inst Tr)))
    (tl : Nat → TreeLot B (Local W₀ Rc ProofFile.Inst Tr))
    (ml : List (MsgLot B (Local W₀ Rc ProofFile.Inst Tr)))
    (hin : (⟨switchNum Zp p 2, fx,
      switchMsgTxt ch Dr readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p 2⟩ :
        MsgLot B (Local W₀ Rc ProofFile.Inst Tr)) ∈ ml)
    (hag : LotsAgree ml (⟨switchNum Zp p 2, fx,
      switchMsgTxt ch Dr readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p 2⟩ :
        MsgLot B (Local W₀ Rc ProofFile.Inst Tr))) :
    OwnMsgs (FirstThread.Script.ofLots bs front cells tok pl tl ml) Vd N (P5J.At.num Zp 24 0) 0
      (k11MaskLot B (Rc := Rc) (Tr := Tr) X ch IM.k11Place (_root_.K11.parOf Zp Bs.G₀) claims
        weights (P5J.At.num Zp 24 0) 3531).txt :=
  ofLots_ownMsgs_of_covers bs front cells tok pl tl ml hin hag
    (k11MaskLot_covered h O hb hB X ch claims weights Dr readers lay hp hl Vd N fx hh hv)

end AtFullSide.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K11.link24Own
#print axioms AtFullSide.K11.link24OwnW
#print axioms AtFullSide.K11.link24OwnW_can_fail
#print axioms AtFullSide.K11.link24Own_at_head
#print axioms AtFullSide.K11.switchNum_at_24
#print axioms AtFullSide.K11.senderLot_mem
#print axioms AtFullSide.K11.k11MaskLot_covered
#print axioms AtFullSide.K11.k11MaskLot_ownMsgs
