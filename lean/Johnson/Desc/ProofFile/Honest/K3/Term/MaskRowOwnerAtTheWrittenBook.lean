-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Term/MaskRowOwnerAtTheWrittenBook.lean: the honest side of the kind
"lookup" (K3), at the full size: who sends each link's mask row, which message of the sending holds
it, where its entries begin among the sender's coins and what its number in the witness is: as closed
facts on written data, evaluated in Lean's kernel; and, over them, the lookups' named premise
`ScriptLaysOwnersCoinsInMaskRow` (Honest/K3/Term/MaskRowFromScript.lean) at each of the 25 links, at a
written owner and a written start, from `OwnMsgs` at the 25 senders' own whole-message texts.

Why. The senders' laws speak in the senders' letters: part 0 at the sender's place, `K1.maskStart` at
a message of the opening, `K2.maskBase` at a message of a switch. The lookups' premise speaks of an
owner and a start. Here both are brought to two written functions of the link,
`maskRowOwnerWritten` and `maskRowStartWritten`. That these are what the book's maker (`ownerOf`)
returns is shown in the side library: AtFullSide/Honest/K3/Term/MaskRowAtEveryLinkFromOwnersTexts.lean.

  `maskRowOwnerWritten`, `maskRowStartWritten`   the owner and the start, by the link
  `openingHoldsMaskRowWritten`           link 0: five closed facts on the opening's written plan
  `openingOwnsLinkZeroWritten`           link 0: owner and start are the opening's own
  `openingPicksMessageZeroWritten`       link 0: the maker's search picks message number 0
  `openingStartIsMessageZerosAlone`      a control: of the opening's messages number 0 alone has that start
  `openingNumberWritten`                 link 0: the number in the witness is the plan's
  `maskRowMessageInSwitch`               which message of a switch: 3 at an odd link, 2 at an even
  `switchOwnsLinksMaskRow`, `switchMessageHoldsOneMaskRow`, `switchMessageBearsPlansNumber`
                                         three closed tests, at a switch's place or a link
  `switchesOwnMaskRowsWritten`, `switchMessagesHoldOneMaskRowWritten`,
  `switchMessagesBearPlansNumbersWritten`   they accept at the written places and links
  `switchesOwnMaskRowsBent`, `switchMessagesBearPlansNumbersBent`   negative tests: at the next message
                                         the first and the third reject everywhere
  `everyLaterLinkHasSwitchWritten`       each link from 1 to 24 has a written place
  `scriptLaysOwnersCoinsAtTheOpening`    link 0: the named premise from `OwnMsgs` at K1's text
  `SwitchTextsAnswer`                    K2's three conditions, not shown here: a definition
  `scriptLaysOwnersCoinsAtASwitch`       links 1 to 24: the named premise from `OwnMsgs` at K2's text
  `scriptLaysOwnersCoinsAtEveryLink`     all 25
  `openingsNumberIsThePlansNumber`, `switchNumberIsThePlansNumber`   the numbers, under the head

Limits. At the full size, at the earlier hash. The written values' own limits stand (the heads of
Honest/K2/Law/PlacesWritten.lean, Johnson/Desc/K1/Law/TiesWritten.lean, Johnson/P5T/PlanSeatsFull.lean).
`OwnMsgs` at the owners' texts is a premise: no Script is laid here. `SwitchTextsAnswer` is a premise:
`closingOk`, that the frame hands a switch's part its coins, and `publicOk` at every valid input are
shown here at no place. Nothing is claimed on soundness, completeness, hiding or any other property
of a protocol.

The lines named …Bent or …Alone are controls on public written numbers: each shows that its
evaluation can come out otherwise. Options: maxRecDepth is raised, and maxHeartbeats lifted, in front
of evaluations: limits on Lean's own work; none loosens a check on a proof.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.OwnersTextsCoverTheMaskRow
import Johnson.Desc.ProofFile.Honest.K1.Law.HasCoinsAtBook
import Johnson.Desc.ProofFile.Honest.K1.Law.K1NumAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.OwnerAtWritten
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchNumsAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicAtHead
import Johnson.P2LawR.MasksAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.K1 (parGF qFull firstPar gpOf seatOfMsg)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (messagesAt)
open VerifiableInference.OnPublicFiles (maskOwnIx)
open Johnson.Prover.Send (shapeAt)
open ProofFile.Honest.FirstThread (Script OwnMsgs)
open ProofFile.Honest.K1 (rideOf firstFold placeJob PlaceIn)
open ProofFile.Honest.K2 (SwitchPlace switchSent switchFresh maskBase maskLength switchPlaces switchNum
  switchNumIn)
open ProofFile.Honest.K2.Law (placesW)
open Johnson.G (proofSendsFull)
open P5T (seatsAllFull)
open P5J (AtMgA TS F0T)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)

/-! ## 1 The owner and the start, written -/

/-- The part that sends link l's mask row: part 0 of the opening at link 0; part 0 of the switch into
the link at a later one. Written. -/
def maskRowOwnerWritten (l : Nat) : Addr :=
  if l = 0 then ⟨⟨1, some 0, 1, .K1⟩, 0⟩ else ⟨⟨1, some l, if l = 24 then 2 else 1, .K2⟩, 0⟩

/-- Where, among that part's coins of the extension field, the row's entries begin. Written. -/
def maskRowStartWritten (l : Nat) : Nat := if l = 0 then 0 else 439

/-! ## 2 Link 0: the opening (K1), closed facts -/

set_option maxRecDepth 1000000 in
/-- **The opening's message number 0, at the written plan**: there is such a message; no table rides
there; it has one mask row; its mask code's message length is 8192; its entries begin at the part's
coin number 0. -/
theorem openingHoldsMaskRowWritten :
    0 < parGF.sent.size ∧ (rideOf (firstFold qFull) 0).isNone = true ∧
      (shapeAt parGF 0).maskRows = 1 ∧
      (parGF.codes.mask.getD (shapeAt parGF 0).maskCode default).ell = 8192 ∧
      K1.maskStart parGF (rideOf (firstFold qFull)) 0 = 0 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **Link 0: the written owner is part 0 at the opening's place; the written start is the opening's
own start of message number 0's mask row.** -/
theorem openingOwnsLinkZeroWritten : (⟨parGF.place, 0⟩ : Addr) = maskRowOwnerWritten 0 ∧
    K1.maskStart parGF (rideOf (firstFold qFull)) 0 = maskRowStartWritten 0 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The maker's search picks message number 0 of the first written sending. -/
theorem openingPicksMessageZeroWritten : (proofSendsFull.1.sends.head?.map fun x =>
    (x.label, x.sent.findIdx isMaskRowMsg)) = some ("link 0, moment 0", 0) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: of the opening's messages number 0 alone has that start. -/
theorem openingStartIsMessageZerosAlone : ((List.range parGF.sent.size).filter fun n =>
    K1.maskStart parGF (rideOf (firstFold qFull)) n == 0) = [0] := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **Link 0: the number, at the written seats**: the plan's numbering at the seat of the opening's
message number 0 gives the plan's number of link 0's own message that has a mask row. -/
theorem openingNumberWritten :
    P5T.arrOf seatsAllFull (seatOfMsg parGF 0 0).1 (seatOfMsg parGF 0 0).2 =
      P5T.numOfPlan seatsAllFull 0 ((maskOwnIx P2Law.K3M.sentW 0).getD 0) := by
  decide +kernel

/-! ## 3 Links 1 to 24: the switches (K2), closed facts -/

/-- Which message of the switch into link l holds that link's mask row: number 3 at an odd link,
number 2 at an even one. -/
def maskRowMessageInSwitch (l : Nat) : Nat := if l % 2 = 1 then 3 else 2

/-- **The first closed test, at a switch's place p**: the written owner of the link into which it
leads is part 0 at p's place; the written start is the switch's own start of message n's mask rows.
-/
def switchOwnsLinksMaskRow (n : Nat) (p : SwitchPlace) : Bool :=
  decide ((⟨p.place, 0⟩ : Addr) = maskRowOwnerWritten p.link) &&
    maskBase p.sizes.codes (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars) n == maskRowStartWritten p.link

/-- **The second closed test, at a switch's place p**: n is a message of the sending and not the
last; it has one mask row; its mask rows have at least 8192 entries; it is the first message of the
sending with main rows and mask rows. -/
def switchMessageHoldsOneMaskRow (n : Nat) (p : SwitchPlace) : Bool :=
  decide (n < (switchSent p.sizes p.others).size) &&
    decide (n ≠ (switchSent p.sizes p.others).size - 1) &&
    ((switchSent p.sizes p.others).getD n default).shape.maskRows == 1 &&
    decide (8192 ≤ maskLength p.sizes.codes (switchSent p.sizes p.others) n) &&
    (switchSent p.sizes p.others).findIdx isMaskRowMsg == n

/-- **The third closed test, at a link l**: the number of message n of the sending "link l, moment 0"
at the written seats is the plan's number of the link's own message that has a mask row. -/
def switchMessageBearsPlansNumber (n l : Nat) : Bool :=
  switchNumIn seatsAllFull l n ==
    P5T.numOfPlan seatsAllFull l ((maskOwnIx P2Law.K3M.sentW l).getD 0)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The first test accepts at every written place that leads into a link below 25.** -/
theorem switchesOwnMaskRowsWritten : (placesW.all fun p => decide (25 ≤ p.link) ||
    switchOwnsLinksMaskRow (maskRowMessageInSwitch p.link) p) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- BENT: at the next message the first test rejects at every such place. -/
theorem switchesOwnMaskRowsBent : (placesW.any fun p => !decide (25 ≤ p.link) &&
    switchOwnsLinksMaskRow (maskRowMessageInSwitch p.link + 1) p) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The second test accepts at every written place that leads into a link below 25.** -/
theorem switchMessagesHoldOneMaskRowWritten : (placesW.all fun p => decide (25 ≤ p.link) ||
    switchMessageHoldsOneMaskRow (maskRowMessageInSwitch p.link) p) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The third test accepts at every link from 1 to 24.** -/
theorem switchMessagesBearPlansNumbersWritten : ((List.range 24).all fun i =>
    switchMessageBearsPlansNumber (maskRowMessageInSwitch (i + 1)) (i + 1)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- BENT: at the next message the third test rejects at every link from 1 to 24. -/
theorem switchMessagesBearPlansNumbersBent : ((List.range 24).any fun i =>
    switchMessageBearsPlansNumber (maskRowMessageInSwitch (i + 1) + 1) (i + 1)) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Each link from 1 to 24 has a written place. -/
theorem everyLaterLinkHasSwitchWritten :
    ((List.range 24).all fun i => placesW.any fun p => p.link == i + 1) = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-! ## 4 Link 0: the named premise from K1's text -/

/-- **LINK 0: THE NAMED PREMISE FROM `OwnMsgs` AT THE OPENING's OWN TEXT**, at the book of whatever
`onlineProverFromPublicFiles` returns, at every Script over that book. CONDITIONAL on the head, hA, hOwn (at message
number 0 of the opening's job as the record of K1's authors has it) and hCount. -/
theorem scriptLaysOwnersCoinsAtTheOpening (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀)
    {Wa Rca Tra Xa₀ Xa : Type} {P : OnlineProverParts Wa Rca Tra Xa₀ Xa} {A : OnlineProverWithDescription Wa Rca Tra Xa₀ Xa}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {Wl Xi Y Cells Tok : Type} {Q : Script A.B Wl Cells Tok MsgT} (wit : Wl → PlaceIn Xi)
    (own₀ : Y) (first : Nat) (Dd : RowDataOf Xi) {valid : Wl → Prop}
    {challengesInFront messageNumber challengesRead : Nat}
    (hOwn : OwnMsgs Q valid challengesInFront messageNumber challengesRead
      (K1.msgTxt 0 wit
        (placeJob (firstPar A.G.first (gpOf A.Z)) first (firstFold A.G.first) Dd) own₀ 0))
    {count : Nat} (hCount : count ≤ 8192) :
    ScriptLaysOwnersCoinsInMaskRow Q valid challengesInFront messageNumber (maskRowOwnerWritten 0)
      (maskRowStartWritten 0) count := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have hC := K1.hasCoins_two_at_book h hA first Dd (Y := Y) rfl
  have eP : firstPar A.G.first (gpOf A.Z) = parGF := by
    rw [eZ, eG]
    exact VerifiableInference.Desc.K1.eG_atAll h O (VerifiableInference.Desc.K1.pin1_atAll h)
  have eF : firstFold A.G.first = firstFold qFull := by
    rw [eG]
    exact K1.firstFold_shape ((VerifiableInference.Desc.K1.hs_atAll h O
      (VerifiableInference.Desc.K1.pin1_atAll h)).trans rfl)
  rw [eP, eF] at hOwn hC
  obtain ⟨w1, w2, w3, w4, -⟩ := openingHoldsMaskRowWritten
  rw [← openingOwnsLinkZeroWritten.1, ← openingOwnsLinkZeroWritten.2]
  exact scriptLaysOwnersCoinsOfSending wit (placeJob parGF first (firstFold qFull) Dd) own₀ 0
    messageNumber challengesRead count valid challengesInFront w1 (Option.isNone_iff_eq_none.1 w2)
    w3 (Nat.le_trans hCount (Nat.le_of_eq w4.symm)) hC hOwn

/-! ## 5 Links 1 to 24: the named premise from K2's text -/

/-- **K2's three conditions that no file shows at a place**, at the places of a list that lead into
a link below 25: the closing's public test; that the frame hands the switch's part its coins, at all
coins of a run; the lot's public test at every valid input's public instance. With `Sizes.serves`,
`Sizes.roomy` and `placeFits`, which are shown under the head (Honest/K2/Law/PublicAtHead.lean), they
are what K2's authors name as the conditions under which the switch's text answers
(Honest/K2/Law/LotsAnswer.lean). It is a definition: the form of a hypothesis. -/
def SwitchTextsAnswer (Bk : ProverCoinCounts) {W₀ Rc Xi Tr : Type} (D : RowDataOf Xi)
    (lay : OnBytes.Params.ReqLayout) (segs : List K2.SegmentPub)
    (valid : Local W₀ Rc Xi Tr → Prop) (places : List SwitchPlace) : Prop :=
  ∀ p ∈ places, p.link < 25 →
    K2.closingOk K2.freshTable (segs.take p.link) p = true ∧
      (∀ k : Coins Bk, (K2.handed 0 p k).isSome = true) ∧
      ∀ w, valid w → K2.publicOk D lay p (segs.take p.link) w.x = true

variable {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- **A LINK FROM 1 TO 24: THE NAMED PREMISE FROM `OwnMsgs` AT THE SWITCH's OWN TEXT**, at every book
and Script. CONDITIONAL on the head and the opening of the description; hp and hl; K2's three
conditions hClosing, hHanded, hPublic; hOwn, at the message by `maskRowMessageInSwitch`; hCount. -/
theorem scriptLaysOwnersCoinsAtASwitch (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Cells Tok : Type}
    {Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT} (Dd : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (lay : OnBytes.Params.ReqLayout)
    (segs : List K2.SegmentPub) {valid : Local W₀ Rc Xi Tr → Prop}
    {challengesInFront messageNumber challengesRead : Nat} {p : SwitchPlace}
    (hp : p ∈ switchPlaces Zp Bs.G₀) (hl : p.link < 25)
    (hClosing : K2.closingOk K2.freshTable (segs.take p.link) p = true)
    (hHanded : ∀ k : Coins Bk, (K2.handed 0 p k).isSome = true)
    (hPublic : ∀ w, valid w → K2.publicOk Dd lay p (segs.take p.link) w.x = true)
    (hOwn : OwnMsgs Q valid challengesInFront messageNumber challengesRead
      (K2.switchMsgTxt 0 Dd readers (K2.lotClosingAt lay segs) p (maskRowMessageInSwitch p.link)))
    {count : Nat} (hCount : count ≤ 8192) :
    ScriptLaysOwnersCoinsInMaskRow Q valid challengesInFront messageNumber
      (maskRowOwnerWritten p.link) (maskRowStartWritten p.link) count := by
  have hpW : p ∈ placesW := by
    rw [← K2.Law.places_at_head h.toAtMg O]
    exact hp
  have u := List.all_eq_true.1 switchesOwnMaskRowsWritten p hpW
  rw [decide_eq_false (Nat.not_le.2 hl), Bool.false_or] at u
  unfold switchOwnsLinksMaskRow at u
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at u
  have t := List.all_eq_true.1 switchMessagesHoldOneMaskRowWritten p hpW
  rw [decide_eq_false (Nat.not_le.2 hl), Bool.false_or] at t
  unfold switchMessageHoldsOneMaskRow at t
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at t
  obtain ⟨⟨⟨⟨t3, t4⟩, t5⟩, t6⟩, -⟩ := t
  rw [← u.1, ← u.2]
  exact scriptLaysOwnersCoinsOfSwitch Dd readers lay segs p _ messageNumber challengesRead count
    valid challengesInFront t3 t4 t5 (Nat.le_trans hCount t6) hClosing hHanded
    (K2.Law.serves_at_head h.toAtMg O p hp) (K2.Law.roomy_at_head h.toAtMg O p hp)
    (K2.Law.fits_at_head h.toAtMg O p hp) hPublic hOwn

/-! ## 6 All 25 links -/

/-- **AT EACH OF THE 25 LINKS: THE NAMED PREMISE, AT THE WRITTEN OWNER AND START, FROM `OwnMsgs` AT THE
25 SENDERS' OWN WHOLE-MESSAGE TEXTS**, at the book of whatever `onlineProverFromPublicFiles` returns, at every Script over
that book. CONDITIONAL on: the head; hA; hOpening, at message number 0 of the opening; hSwitches, at
each switch that leads into a link below 25, at the message by `maskRowMessageInSwitch`; hAnswer,
K2's three conditions. challengesInFront, messageNumber, challengesRead: letters, by the link. -/
theorem scriptLaysOwnersCoinsAtEveryLink (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀)
    {Wa Rca Tra Xa₀ Xa : Type} {P : OnlineProverParts Wa Rca Tra Xa₀ Xa} {A : OnlineProverWithDescription Wa Rca Tra Xa₀ Xa}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {W₀ Rc Xi Tr Xj Y Cells Tok : Type} {Q : Script A.B (Local W₀ Rc Xi Tr) Cells Tok MsgT}
    {valid : Local W₀ Rc Xi Tr → Prop} {challengesInFront messageNumber challengesRead : Nat → Nat}
    (wit : Local W₀ Rc Xi Tr → PlaceIn Xj) (own₀ : Y) (first : Nat) (openingData : RowDataOf Xj)
    (hOpening : OwnMsgs Q valid (challengesInFront 0) (messageNumber 0) (challengesRead 0)
      (K1.msgTxt 0 wit
        (placeJob (firstPar A.G.first (gpOf A.Z)) first (firstFold A.G.first) openingData) own₀ 0))
    (switchData : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List K2.SegmentPub)
    (hAnswer : SwitchTextsAnswer A.B switchData lay segs valid (switchPlaces A.Z A.G))
    (hSwitches : ∀ p ∈ switchPlaces A.Z A.G, p.link < 25 →
      OwnMsgs Q valid (challengesInFront p.link) (messageNumber p.link) (challengesRead p.link)
        (K2.switchMsgTxt 0 switchData readers (K2.lotClosingAt lay segs) p
          (maskRowMessageInSwitch p.link))) :
    ∀ l, l < 25 → ∀ count, count ≤ 8192 →
      ScriptLaysOwnersCoinsInMaskRow Q valid (challengesInFront l) (messageNumber l)
        (maskRowOwnerWritten l) (maskRowStartWritten l) count := by
  intro l hl count hCount
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  rcases Nat.eq_zero_or_pos l with rfl | h1
  · exact scriptLaysOwnersCoinsAtTheOpening h hA wit own₀ first openingData hOpening hCount
  · obtain ⟨p, hpW, rfl⟩ : ∃ p ∈ placesW, p.link = l := by
      obtain ⟨p, hp, e⟩ := List.any_eq_true.1 (List.all_eq_true.1 everyLaterLinkHasSwitchWritten
        (l - 1) (List.mem_range.2 (by omega)))
      have e' := beq_iff_eq.1 e
      exact ⟨p, hp, by omega⟩
    have hp : p ∈ switchPlaces Zp Bs.G₀ := by
      rw [K2.Law.places_at_head h.toAtMg O]
      exact hpW
    have hpA : p ∈ switchPlaces A.Z A.G := by
      rw [eZ, eG]
      exact hp
    obtain ⟨c1, c2, c3⟩ := hAnswer p hpA hl
    exact scriptLaysOwnersCoinsAtASwitch h O switchData readers lay segs hp hl c1 c2 c3
      (hSwitches p hpA hl) hCount

/-! ## 7 The numbers, under the head -/

/-- Which of a link's own messages has a mask row: the public part's shape is the written one. -/
theorem maskMessageIndexAtHead (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀) (l : Nat) :
    maskOwnIx (P5J.At.sentAt Zp) l = maskOwnIx P2Law.K3M.sentW l := by
  unfold maskOwnIx messagesAt
  rw [show (P5J.At.sentAt Zp).shape = P2Law.K3M.sentW.shape from h.toAtMg.masks_shape_written]

/-- **LINK 0: THE NUMBER UNDER WHICH K1's AUTHORS LAY THE OPENING's MESSAGE NUMBER 0 IS THE PLAN's
NUMBER OF LINK 0's OWN MESSAGE THAT HAS A MASK ROW.** -/
theorem openingsNumberIsThePlansNumber (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    P5J.At.arr Zp (K1.seatAtMember cF.blocksInOrder 2 (firstPar Bs.G₀.first (gpOf Zp)) 0).1
        (K1.seatAtMember cF.blocksInOrder 2 (firstPar Bs.G₀.first (gpOf Zp)) 0).2 =
      P5J.At.num Zp 0 ((maskOwnIx (P5J.At.sentAt Zp) 0).getD 0) := by
  rw [K1.seat_two_written h O 0, maskMessageIndexAtHead h 0]
  show P5T.arrOf (P5J.At.pseatsAll Zp) _ _ = P5T.numOfPlan (P5J.At.pseatsAll Zp) _ _
  rw [K1.pseatsAll_written h]
  exact openingNumberWritten

/-- **A LINK FROM 1 TO 24: K2's NUMBER OF THE SWITCH's MESSAGE IS THE PLAN's NUMBER OF THE LINK's OWN
MESSAGE THAT HAS A MASK ROW.** -/
theorem switchNumberIsThePlansNumber (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x₀)
    (p : SwitchPlace) (h1 : 1 ≤ p.link) (hl : p.link < 25) :
    switchNum Zp p (maskRowMessageInSwitch p.link) =
      P5J.At.num Zp p.link ((maskOwnIx (P5J.At.sentAt Zp) p.link).getD 0) := by
  have t := List.all_eq_true.1 switchMessagesBearPlansNumbersWritten (p.link - 1)
    (List.mem_range.2 (by omega))
  rw [show p.link - 1 + 1 = p.link by omega] at t
  rw [maskMessageIndexAtHead h p.link]
  show switchNumIn (P5J.At.pseatsAll Zp) _ _ = P5T.numOfPlan (P5J.At.pseatsAll Zp) _ _
  rw [K1.pseatsAll_written h]
  exact beq_iff_eq.1 t

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.openingHoldsMaskRowWritten
#print axioms ProofFile.Honest.K3.Term.openingOwnsLinkZeroWritten
#print axioms ProofFile.Honest.K3.Term.openingPicksMessageZeroWritten
#print axioms ProofFile.Honest.K3.Term.openingStartIsMessageZerosAlone
#print axioms ProofFile.Honest.K3.Term.openingNumberWritten
#print axioms ProofFile.Honest.K3.Term.switchesOwnMaskRowsWritten
#print axioms ProofFile.Honest.K3.Term.switchesOwnMaskRowsBent
#print axioms ProofFile.Honest.K3.Term.switchMessagesHoldOneMaskRowWritten
#print axioms ProofFile.Honest.K3.Term.switchMessagesBearPlansNumbersWritten
#print axioms ProofFile.Honest.K3.Term.switchMessagesBearPlansNumbersBent
#print axioms ProofFile.Honest.K3.Term.everyLaterLinkHasSwitchWritten
#print axioms ProofFile.Honest.K3.Term.scriptLaysOwnersCoinsAtTheOpening
#print axioms ProofFile.Honest.K3.Term.scriptLaysOwnersCoinsAtASwitch
#print axioms ProofFile.Honest.K3.Term.scriptLaysOwnersCoinsAtEveryLink
#print axioms ProofFile.Honest.K3.Term.maskMessageIndexAtHead
#print axioms ProofFile.Honest.K3.Term.openingsNumberIsThePlansNumber
#print axioms ProofFile.Honest.K3.Term.switchNumberIsThePlansNumber
