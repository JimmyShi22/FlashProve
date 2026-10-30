-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
ON PUBLIC DATA, UNDER THE LIBRARY's HEAD ON THE PUBLIC INPUT.
Johnson/Desc/ProofFile/Honest/K3/Term/SymbolSeatsAtEveryLink.lean: the honest side of the kind
"lookup" (K3): ON PUBLIC DATA, under the library's head on the public input (`P5J.AtMgA`): at every
link, every matrix of the link's list (THE PLANES' TOO) and every committed symbol of it: the
symbol's address has a seat among the messages that stand sent at the calls' lookup; the seat lies
in its message's main rows and off the pad; the array, the place by the layout's rule and the
number in the witness at that seat are the owner's.

Why. The lookup's callers read the trace's cells off committed symbols (`symAt`,
Johnson/Desc/First/Look/K3CallerAtt.lean); the senders' sentence on the `Script` (`LaysFilling`,
Honest/K5/Law/LaysFilling.lean) speaks at the owner's segment, the array's own message and the
layout's rule. This file ties the first to the second. The kind K5 has both laws at attention's
twelve links (`symsRoom_head`, Honest/K5/Law/CellsQAtHead.lean; `seat_number_head`,
Honest/K5/Law/SeatNumber.lean); these are their texts at a link whatever, over the library's two
public ties in place of that kind's condition.

  `oneNumberTestAcceptsAtEveryLink`   the named test `AtMgA.oneC` accepts at all 25 links, from the head
  `symbolsRoomAtEveryLink`     `SymsRoom` (Honest/K5/Law/CellsQRaw.lean) at every matrix of the list
  `seatNumberAtEveryLink`      the entry of the list of arrays, the array, the place, the number

How. `P5J.k03_tie_head` (Johnson/P5J/K03TieHead.lean): the test "tie" at all 25 links, from the head
alone. `P5J.AtMgA.one_at` (Johnson/P5J/K03OneOwnAt.lean): "one number", from the named test
`AtMgA.oneC`, a premise of the two laws (`oneAccepts`), which `oneNumberTestAcceptsAtEveryLink` pays: below
24 by the library's `oneC_at_head` (Johnson/Desc/First/Att/Door/Law/K5OneOfHead.lean), at 24 by that
law's own proof over one more decision of the kernel (Term/OneNumberTestAtTheHeadsLink.lean).
`Meaning.seat_of_tie` (Johnson/Goal/Meaning/ReadingsOne.lean).

Limits. CONDITIONAL on the head. The tail is `Meaning.tlAt`'s. Of what a message
holds nothing is said. It rests on closed facts that Lean's kernel decided by evaluation at the
library's written values. The full size and the earlier hash alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SeatNumber
import Johnson.P5J.K03TieHead
import Johnson.P5J.K03OneOwnAt
import Johnson.Desc.First.Att.Door.Law.K5OneOfHead
import Johnson.Desc.ProofFile.Honest.K3.Term.OneNumberTestAtTheHeadsLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (Seat seatCalls sigListCalls)
open ProofFile.Honest.K5 (SymsRoom msgNo5 msgNo5_congr)
open P5J (AtMgA TS)

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : PlaceL} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)

/-- **THE NAMED TEST "one" ACCEPTS AT ALL 25 LINKS, FROM THE HEAD ALONE.** Below 24: the library's. At
24: `H2K5.Door.oneC_at`'s own proof, over the closed fact at link 24. -/
theorem oneNumberTestAcceptsAtEveryLink {link : ℕ} (linkBelow : link < 25) :
    h.oneC link = true := by
  by_cases h24 : link < 24
  · exact H2K5.Door.oneC_at_head h h24
  · obtain rfl : link = 24 := by omega
    have hy : VerifiableInference.PlanWritten.madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first
        Zp.made = true :=
      VerifiableInference.PlanWritten.pinnedAt_of_row (by rw [h.toAtMg.pins.1, Bool.or_true])
    have A := VerifiableInference.Desc.First.K2Ties.at_written h.scope h.laid hy
    have hx := VerifiableInference.PlanWritten.Joined.xShape_in_scope h.scope h.laid.pub hy
    have hF : _root_.Meaning.NamedAsk.fullShaped Zp.p.X = true :=
      _root_.Meaning.NamedAsk.fullShaped_scope h.scope h.reads h.pubOne
    show P5J.K03.oneB Zp.p.X (P5J.At.sentAt Zp) (P5J.At.rad3At Zp Z.lay) (P5J.At.num Zp)
      (VerifiableInference.Desc.First.Look.idxAt (P5J.At.sentAt Zp) (P5J.At.num Zp) 24)
      (_root_.Meaning.tlAt Zp.p.X) 24
      (fun j => P6T.seatCallsT (P5J.At.pseats Zp) (P5J.At.sentAt Zp) 24 j) (P5J.At.arr Zp) id = true
    rw [H2K5.Door.oneB_view hF _ _ _ _ _ (by decide : 24 < 25), hx,
      H2K5.Door.oneV_sent _ (D' := H2K5.Door.sentW) (show P5J.At.shape Zp = _ from A.shape)
        (show P5J.At.layout Zp = _ from A.layout), A.num, A.pseats, A.arr]
    exact oneNumberTestAcceptsAtTheHeadsLinkAtWrittenValues

/-- **THE SYMBOLS' ROOM AT EVERY MATRIX OF THE LIST, AT EVERY LINK.** CONDITIONAL: under the head h;
the place's link is below 25; the named test "one" accepts there; the matrix's number is below the
record's number of matrices. The place is read at its link alone. -/
theorem symbolsRoomAtEveryLink {x : PlaceL} (linkBelow : x.link < 25)
    (oneAccepts : h.oneC x.link = true) {number : ℕ}
    (numberBelow : number < (_root_.Meaning.tlAt (P5J.At.X Zp) x.link).NM) :
    SymsRoom h.𝔇.sent h.𝔇.l3.rad x (_root_.Meaning.tlAt (P5J.At.X Zp) x.link) number := by
  have T : _root_.Meaning.linkTieB (P5J.At.X Zp) h.𝔇.sent h.𝔇.rad3 (P5J.At.num Zp)
      (VerifiableInference.Desc.First.Look.idxAt (P5J.At.sentAt Zp) (P5J.At.num Zp) x.link) x.link
      (_root_.Meaning.tlAt (P5J.At.X Zp) x.link) = true := P5J.k03_tie_head h linkBelow
  have O1 : VerifiableInference.OnPublicFiles.OneNumber (P5J.At.X Zp) h.𝔇.sent h.𝔇.rad3 (P5J.At.num Zp)
      (VerifiableInference.Desc.First.Look.idxAt (P5J.At.sentAt Zp) (P5J.At.num Zp) x.link)
      (_root_.Meaning.tlAt (P5J.At.X Zp)) x.link
      (fun j : Fin (sigListCalls h.𝔇.sent h.𝔇.rad3 x.link).length => h.𝔇.seat3 x.link false j.1)
      h.𝔇.arr id := h.one_at linkBelow oneAccepts
  intro i' c hi' hc
  obtain ⟨hs, hk, hf⟩ := _root_.Meaning.seat_of_tie T (μ := number) (i := i') (c := c) numberBelow
    hi' hc
  rw [if_neg (by simp)] at hf
  have O := O1 number i' c numberBelow hi' hc hk
  exact ⟨_, hk, hs, hf.1, hf.2, O.1⟩

/-- **THE ARRAY, THE ENTRY, THE PLACE AND THE NUMBER AT A SYMBOL's SEAT, AT EVERY LINK.**
CONDITIONAL: as above; the symbol lies inside the matrix's packed rows and its columns; its address
has the seat s, whose member is in the list. -/
theorem seatNumberAtEveryLink {x : PlaceL} (linkBelow : x.link < 25)
    (oneAccepts : h.oneC x.link = true) {number symbolRow column : ℕ}
    (numberBelow : number < (_root_.Meaning.tlAt (P5J.At.X Zp) x.link).NM)
    (symbolRowBelow : symbolRow <
      Alg.symRows ((_root_.Meaning.tlAt (P5J.At.X Zp) x.link).mats.getD number {}).m)
    (columnBelow : column < ((_root_.Meaning.tlAt (P5J.At.X Zp) x.link).mats.getD number {}).k)
    {s : Seat} (memberInTheList : s.msg < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x.link).length)
    (seatIsFound : seatCalls h.𝔇.sent x.link
      (.cell ((_root_.Meaning.tlAt (P5J.At.X Zp) x.link).gtTree.getD number 0) symbolRow column) =
        some s) :
    ∃ A : OnBytes.Params.ReqArray,
      (h.𝔇.sent.arrayOf.getD x.link #[])[(_root_.Meaning.tlAt (P5J.At.X Zp) x.link).gtTree.getD
          number 0]? =
        some (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) x.link number),
          Meaning.nameOf (Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) x.link number))) ∧
      VerifiableInference.Desc.arrayOf h.𝔇.sent.layout
        (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) x.link number))
        (Meaning.nameOf (Meaning.ownerA (Meaning.labAt (P5J.At.X Zp) x.link number))) = some A ∧
      VerifiableInference.Desc.laidAt A symbolRow column = some (s.row, s.place) ∧
      msgNo5 h x s.msg memberInTheList =
        P5J.At.num Zp (Meaning.ownerK (Meaning.labAt (P5J.At.X Zp) x.link number)) A.message := by
  have T : _root_.Meaning.linkTieB (P5J.At.X Zp) h.𝔇.sent h.𝔇.rad3 (P5J.At.num Zp)
      (VerifiableInference.Desc.First.Look.idxAt (P5J.At.sentAt Zp) (P5J.At.num Zp) x.link) x.link
      (_root_.Meaning.tlAt (P5J.At.X Zp) x.link) = true := P5J.k03_tie_head h linkBelow
  have O1 : VerifiableInference.OnPublicFiles.OneNumber (P5J.At.X Zp) h.𝔇.sent h.𝔇.rad3 (P5J.At.num Zp)
      (VerifiableInference.Desc.First.Look.idxAt (P5J.At.sentAt Zp) (P5J.At.num Zp) x.link)
      (_root_.Meaning.tlAt (P5J.At.X Zp)) x.link
      (fun j : Fin (sigListCalls h.𝔇.sent h.𝔇.rad3 x.link).length => h.𝔇.seat3 x.link false j.1)
      h.𝔇.arr id := h.one_at linkBelow oneAccepts
  have t := List.all_eq_true.1 T number (List.mem_range.2 numberBelow)
  unfold _root_.Meaning.entryTieB at t
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at t
  obtain ⟨⟨t1, -⟩, -⟩ := t
  obtain ⟨bn, hbn, h1⟩ := Option.bind_eq_some_iff.1 seatIsFound
  obtain ⟨A, hA, h2⟩ := Option.bind_eq_some_iff.1 h1
  obtain ⟨rp, hrp, h3⟩ := Option.bind_eq_some_iff.1 h2
  obtain rfl := Option.some.inj (hbn.symm.trans t1)
  have hA' : VerifiableInference.Desc.arrayOf h.𝔇.sent.layout
      (_root_.Meaning.ownerK (_root_.Meaning.labAt (P5J.At.X Zp) x.link number))
      (_root_.Meaning.nameOf (_root_.Meaning.ownerA
        (_root_.Meaning.labAt (P5J.At.X Zp) x.link number))) = some A := hA
  have hrp' : VerifiableInference.Desc.laidAt A symbolRow column = some rp := by
    rw [← _root_.Meaning.laidPlace_eq_laidAt]
    exact hrp
  have hrow : rp = (s.row, s.place) := by
    split at h3
    · obtain rfl := Option.some.inj h3
      rfl
    · obtain ⟨j, -, rfl⟩ := Option.map_eq_some_iff.1 h3
      rfl
  have eF : _root_.Meaning.fLay h.𝔇.sent.layout (P5J.At.num Zp)
      (_root_.Meaning.labAt (P5J.At.X Zp) x.link number) symbolRow column =
      (P5J.At.num Zp (_root_.Meaning.ownerK (_root_.Meaning.labAt (P5J.At.X Zp) x.link number))
        A.message, rp.1, rp.2) := by
    unfold _root_.Meaning.fLay VerifiableInference.Desc.seatIn
    rw [hA']
    show ((VerifiableInference.Desc.laidAt A symbolRow column).map fun y =>
      (P5J.At.num Zp (_root_.Meaning.ownerK (_root_.Meaning.labAt (P5J.At.X Zp) x.link number))
        A.message, y.1, y.2)).getD (0, 0, 0) = _
    rw [hrp']
    rfl
  obtain ⟨hs2, hk2, -⟩ := _root_.Meaning.seat_of_tie T (μ := number) (i := symbolRow)
    (c := column) numberBelow symbolRowBelow columnBelow
  have es := Option.some.inj (seatIsFound.symm.trans hs2)
  have O := (O1 number symbolRow column numberBelow symbolRowBelow columnBelow hk2).2
  refine ⟨A, t1, hA', by rw [hrp', hrow], ?_⟩
  have em : s.msg = VerifiableInference.Desc.First.Look.idxAt (P5J.At.sentAt Zp) (P5J.At.num Zp)
      x.link (_root_.Meaning.fLay h.𝔇.sent.layout (P5J.At.num Zp)
      (_root_.Meaning.labAt (P5J.At.X Zp) x.link number) symbolRow column).1 := by
    rw [es]
  refine (msgNo5_congr h em (hk' := hk2)).trans (O.trans ?_)
  rw [eF]
  rfl

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.oneNumberTestAcceptsAtEveryLink
#print axioms ProofFile.Honest.K3.Term.symbolsRoomAtEveryLink
#print axioms ProofFile.Honest.K3.Term.seatNumberAtEveryLink
