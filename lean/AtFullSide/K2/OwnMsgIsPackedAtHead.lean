-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/OwnMsgIsPackedAtHead.lean: the kind "the code switch" (K2): `msg_own_packed`
(Johnson/Desc/ProofFile/Honest/K2/Law/OwnMsgIsPacked.lean) under the library's head, at the book
that the maker lays: at a fit joined list that holds the switches' share at the plan's own letters
(`switchShareAt`, Honest/K2/JoinShare.lean), the joined `Script`'s witness holds, in the message
with the plan's number of (link l, the array's message), at the layout's place of each element of an
array "M mu" of a link l from 1 to 24, the packing of the reader's cells of (l, mu). Three
definitions: a public test. Lemmas; none of the library's goals. It lies in the side library because
it imports files of it.

  `ownArrayOk`         A PUBLIC TEST on a written place and an array of its link: the array's
                       message is one of the switch's own; its address has the seat (link, message);
                       the switch is its first sender; the place's codes are the written ones; the
                       message fits; the values' size is the array's; the sending's shape there is
                       the request's; its code is there, with a power of two for its length. With
                       three bends for the controls, 0 in earnest
  `ownArraysOk`, `ownArraysAny`   the test at all, and the bent test at some, of the arrays of the
                       written places' links whose names read as numbers
  `ownArraysW`         BY LEAN's KERNEL: the test says yes at all of them
  `ownArraysW_small`, `_seat`, `_shape`, `_own`   CONTROLS THAT SAY NO: at the small example's
                       sizes; at the next own message's address, at the next link's shapes, and
                       counted three further among the switch's own: there none passes
  `ownArraysW_count`   there are 143 such arrays: so the first is not idle
  `linksW`             BY LEAN's KERNEL: each link from 1 to 24 has a written place
  `msg_owner_at_head`  THE END

By, of other authors: `first_at_head`, `switchSeat_at_head`, `publicOk_of_two`
(Honest/K2/Law/LightAtHead.lean) · `labelNo_eq`, `cellsVals_eq` (LabelByList.lean there) ·
`msgTxt_answers_two` (LotsAnswerAtHead.lean) · `msgTxt_inv` (MainTxt.lean) · `noWord_open`
(SampledOpen.lean) · `places_at_head` (PlacesWritten.lean) · `labelNo_arrayLabel`
(Honest/K5/Law/PackedVals.lean) · `Meaning.arrayOf_mem` (Johnson/Goal/Meaning/LaidInsideSeats.lean).
And: `handed_at_book` (HandedAtTheBook.lean of this folder) · `ownRole_at_head`, `ownNums_at_head`
(Honest/K2/Law/OwnRolesAtHead.lean) · `digits_light_at_head` (DigitsLightAtHead.lean there).

What stays a hypothesis in the end. h, O: the library's head and the opening. hB: B is the book that
the maker lays. F, hin: the list is fit and holds the switches' share. hD: the light test at the
reads' filling says yes at each instance that passes `okStart`; proved by nobody. hx: the input's
instance passes `okStart`. h1, hl, hmu: l is from 1 to 24 and mu below 26. hA, hi, hc, hrp: the
layout has the array, the element lies inside it, and rp is its place.

Limits. An equation on the Script's witness, at each run's coins: what is written where. The coins
stand on the left alone, inside the witness; the right side is a function of what the reader yields
of the input. It belongs to the argument that an honest run is accepted, and is not to be quoted
beside a law over coins. It speaks of the reader's cells (`readers w`): that these are any trace's
is not said. At link 0 nothing is said: there the arrays stand in another kind's sending. A matrix
that a segment borrows has no array of that segment: it is spoken of at its owner's link alone. The
switches' data are laid at one choice of sizes (`Sz.ref`). Chain 0 alone. The full size; the
format's second hash function. Closed facts by Lean's kernel, with an option raised. `Meaning.arrayOf_mem`
brings in LaidInsideSeats.lean with that file's own imports. That the joined Script is the honest
prover's is not said here: it is laid from lots, and holds what their texts say. This file proves
nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import AtFullSide.K2.HandedAtTheBook
import Johnson.Desc.ProofFile.Honest.K2.Law.OwnMsgIsPacked
import Johnson.Desc.ProofFile.Honest.K2.Law.DigitsLightAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.LotsAnswerAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.OwnRolesAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.SampledOpen
import Johnson.Desc.ProofFile.Honest.K5.Law.PackedVals
import Johnson.Goal.Meaning.LaidInsideSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open OnBytes.HonestTrace (Sz packedCells)
open OnBytes.Params (ReqArray)
open VerifiableInference.Desc (Block Chain arrayOf laidAt)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.G (layoutFull proofSendsFull)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.FirstThread (TreeLot Others joinQ JoinFit)
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law

/-! ## 1 The written data -/

/-- **A PUBLIC TEST** on a place and an array of its link, at the values' sizes S₀. d, e, f: three
bends for the controls, 0 in earnest: the own message's address d further; the request's link e
further; the array's message counted f further among the switch's own. -/
def ownArrayOk (S₀ : Sz) (d e f : ℕ) (p : SwitchPlace) (A : ReqArray) : Bool :=
  decide (A.message + f < p.others.size - 1) &&
    switchSeatW (p.ownAddr (A.message + d)) == some (p.link, A.message) &&
    firstSender p (1 + p.sizes.kept.length + A.message) &&
    decide (p.sizes.codes = proofSizedFull.codes) &&
    msgFits proofSizedFull.codes proofSizedFull.request layoutFull p.link A.message &&
    (cellsValsL S₀).size p.link A.name == some (A.sizeI, A.sizeC) &&
    match (proofSizedFull.request.link.getD (p.link + e) default).messages[A.message]? with
    | none => false
    | some M =>
      decide (((switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + A.message)
        default).shape = M.shape) &&
        match proofSizedFull.codes.base[M.shape.code]? with
        | none => false
        | some cd => OnBytes.powerOfTwo cd.ell

/-- The test at each written place, at each array of its link whose name reads as a number. -/
def ownArraysOk (S₀ : Sz) : Bool :=
  placesW.all fun p => (layoutFull.link.getD p.link []).all fun A =>
    !(labelNoL A.name).isSome || ownArrayOk S₀ 0 0 0 p A

/-- Some such array of some written place passes the bent test. -/
def ownArraysAny (d e f : ℕ) : Bool :=
  placesW.any fun p => (layoutFull.link.getD p.link []).any fun A =>
    (labelNoL A.name).isSome && ownArrayOk Sz.ref d e f p A

set_option maxRecDepth 1000000 in
/-- **At the written data the test says yes.** -/
theorem ownArraysW : ownArraysOk Sz.ref = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at the small example's sizes it says no. -/
theorem ownArraysW_small : ownArraysOk Sz.small = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at the address of the next own message no array passes. -/
theorem ownArraysW_seat : ownArraysAny 1 0 0 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at the next link's shapes no array passes. -/
theorem ownArraysW_shape : ownArraysAny 0 1 0 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: counted three further among the switch's own messages no array passes. -/
theorem ownArraysW_own : ownArraysAny 0 0 3 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- There are 143 such arrays. -/
theorem ownArraysW_count :
    (placesW.map fun p =>
      ((layoutFull.link.getD p.link []).filter fun A => (labelNoL A.name).isSome).length).foldl
        (· + ·) 0 = 143 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **Each link from 1 to 24 has a written place.** -/
theorem linksW : ((List.range 24).all fun i => placesW.any fun p => p.link == i + 1) = true := by
  decide +kernel

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {B : ProverCoinCounts}

/-- **THE WITNESS's MESSAGE OF THE PLAN's NUMBER HOLDS THE PACKING OF THE READER's CELLS**, at each
array "M mu" of a link from 1 to 24. -/
theorem msg_owner_at_head {W₀ Rc Tr Xj Y Cells Tok : Type}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (front : Nat) (seats : List (Nat × Nat))
    (wit : Local W₀ Rc ProofFile.Inst Tr → K1.PlaceIn Xj) (own₀ : Y)
    (jobs : List (Nat × K1.SendJob (K1.PlaceIn Xj) Y))
    (Oth : Others B (Local W₀ Rc ProofFile.Inst Tr)) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (rest : Nat → TreeLot B (Local W₀ Rc ProofFile.Inst Tr))
    (F : JoinFit cF.blocksInOrder front (P5J.At.arr Zp) seats wit own₀ jobs Oth)
    (hin : ShareIn (switchShareAt B cF.blocksInOrder front Zp Bs.G₀
      (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) readers rest) Oth)
    (cells : Local W₀ Rc ProofFile.Inst Tr → Cells) (tok : Local W₀ Rc ProofFile.Inst Tr → Tok)
    (hD : ∀ ξ, (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true → ReadsLight Zp Bs.G₀ ξ)
    {l : ℕ} (h1 : 1 ≤ l) (hl : l < 25) {mu : ℕ} (hmu : mu < 26) {A : ReqArray}
    (hA : arrayOf (P5J.At.layout Zp) l (Meaning.nameOf mu) = some A) (k : Coins B)
    (w : Local W₀ Rc ProofFile.Inst Tr) (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart w.x = true)
    (hd : List Fmt.Drawn) {i c : ℕ} (hi : i < A.sizeI) (hc : c < A.sizeC) {rp : ℕ × ℕ}
    (hrp : laidAt A i c = some rp) :
    ((joinQ cF.blocksInOrder front cells tok (P5J.At.arr Zp) wit own₀ jobs Oth).wit k w hd).msg
        (P5J.At.num Zp l A.message) false rp.1 rp.2 =
      algebraMap Cb.Gl.F Cb.Gl.E (packedCells Sz.ref (readers w).cells.cell l mu i c) := by
  obtain ⟨e1, e2, e3⟩ := first_at_head h O
  -- the array, in the written layout
  have eL : P5J.At.layout Zp = layoutFull := by
    rw [← e3, O.first]
    rfl
  rw [eL] at hA
  obtain ⟨as, has, hAs⟩ := Meaning.arrayOf_mem hA
  have hname : A.name = OnBytes.HonestTrace.arrayLabel mu := by
    unfold arrayOf at hA
    rw [has] at hA
    have hA' : as.find? (fun a => a.name == Meaning.nameOf mu) = some A := hA
    have q : (A.name == Meaning.nameOf mu) = true :=
      List.find?_some (p := fun a : ReqArray => a.name == Meaning.nameOf mu) hA'
    exact eq_of_beq q
  have hlab : K1.labelNo A.name = some mu := by
    rw [hname]
    exact K5.labelNo_arrayLabel hmu
  have hAl : A ∈ layoutFull.link.getD l [] := by
    rw [List.getD_eq_getElem?_getD, has]
    exact hAs
  -- the place
  obtain ⟨p, hpW, epl⟩ := List.any_eq_true.1
    (List.all_eq_true.1 linksW (l - 1) (List.mem_range.2 (by omega)))
  have epl' : p.link = l := by
    have q := eq_of_beq epl
    omega
  subst epl'
  have hp : p ∈ switchPlaces Zp Bs.G₀ := by
    rw [places_at_head h.toAtMg O]
    exact hpW
  -- the test
  have T : ownArrayOk Sz.ref 0 0 0 p A = true := by
    have q := List.all_eq_true.1 (List.all_eq_true.1 ownArraysW p hpW) A hAl
    rw [← labelNo_eq, hlab] at q
    exact q
  unfold ownArrayOk at T
  simp only [Nat.add_zero, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at T
  obtain ⟨⟨⟨⟨⟨⟨T1, T2⟩, T3⟩, T4⟩, T5⟩, T6⟩, T7⟩ := T
  cases hM : (proofSizedFull.request.link.getD p.link default).messages[A.message]? with
  | none => rw [hM] at T7; cases T7
  | some M =>
    rw [hM] at T7
    simp only [Bool.and_eq_true, decide_eq_true_eq] at T7
    obtain ⟨T8, T9⟩ := T7
    cases hcd : proofSizedFull.codes.base[M.shape.code]? with
    | none => rw [hcd] at T9; cases T9
    | some cd =>
      rw [hcd] at T9
      -- the text answers
      obtain ⟨y, hy⟩ := msgTxt_answers_two h.toAtMg O 0
        (withSwitchData Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀) readers Bs.G₀.first.layout hp
        (1 + p.sizes.kept.length + A.message) k w
        (hd.take (front + roundsTo cF.blocksInOrder (borderNo cF.blocksInOrder p.place))) false rp.1 rp.2
        (handed_at_book h O hB hp k)
        (publicOk_of_two h O (digits_light_at_head h O) (hD w.x hx) p hp)
      obtain ⟨cn, V, hH, hV⟩ := msgTxt_inv hy
      have hn := (ownRole_at_head h.toAtMg O p hp A.message T1).1
      rw [← ownNums_at_head h.toAtMg O p hp A.message T1]
      exact msg_own_packed 0 (coreSender freshTable) Sz.ref (K1.lotData Sz.ref) Zp Bs.G₀ readers
        (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) (fun p => borderNo cF.blocksInOrder p.place)
        (fun p => front + roundsTo cF.blocksInOrder (borderNo cF.blocksInOrder p.place)) (switchNum Zp)
        (fun p =>
          ((switchSeatIn (P5J.At.pseatsAll Zp) p.link 0).map fun q : P5T.PSeat => q.j).getD 0)
        (fun p n =>
          ((switchSeatIn (P5J.At.pseatsAll Zp) p.link n).map fun q : P5T.PSeat => q.t).getD 0)
        (switchPlaces Zp Bs.G₀) rest F hin cells tok (fun _ => True) hp (noWord_open O p hp) hn T3
        k hH w trivial hd hV (by rw [switchSeat_at_head h O]; exact T2) (by rw [e2]; exact hM) T8
        (T4.trans e1.symm) (by rw [e1]; exact hcd) T9 (by rw [e1, e2, e3]; exact T5)
        (by rw [e3]; exact List.mem_filter.2 ⟨hAl, beq_self_eq_true _⟩) hrp hlab
        (by rw [cellsVals_eq]; exact T6) ⟨hi, hc⟩

end AtFullSide.K2

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K2.ownArrayOk
#print axioms AtFullSide.K2.ownArraysOk
#print axioms AtFullSide.K2.ownArraysAny
#print axioms AtFullSide.K2.ownArraysW
#print axioms AtFullSide.K2.ownArraysW_small
#print axioms AtFullSide.K2.ownArraysW_seat
#print axioms AtFullSide.K2.ownArraysW_shape
#print axioms AtFullSide.K2.ownArraysW_own
#print axioms AtFullSide.K2.ownArraysW_count
#print axioms AtFullSide.K2.linksW
#print axioms AtFullSide.K2.msg_owner_at_head
