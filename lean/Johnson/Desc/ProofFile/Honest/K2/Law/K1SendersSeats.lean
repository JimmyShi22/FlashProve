-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/K1SendersSeats.lean: WHERE THE MESSAGES OF THE SENDERS OF THE
KIND K1 SIT AMONG A CLOSED GROUP's MEMBERS, UNDER THE HEAD: WHICH MEMBER OF ITS LINK's WRITTEN LIST
EACH IS, THAT THE MEMBER HAS THE MESSAGE's SHAPE, AND THAT THE MEMBER's SEAT (`seatK10`; for the
first segment's fresh mask `maskTree`, `maskPart`) IS THE SENDER's OWN SEAT (`K1.seatAtMember`): SO
THAT THE TABLE's NUMBER AT THE MEMBER's SEAT IS THE SENDER's OWN NUMBER `K1.k1Num`. PUBLIC DATA
ALONE: written lists of seats and shapes. The sister of SeatIsK10.lean of this folder, which stands
at the switches' sendings. Three definitions: a public test; that test laid at the two sorts of
member. Lemmas; none of the library's goals.

  `k1SeatTie` ps l pos seat sh
      A PUBLIC TEST: the list of link l's members has a member at position pos; among the link's
      sampled seats it sits at seat; its shape is sh
  `k1SeatTie_gives`
      what its yes gives: the member i, `seatK10` (loAt l) ps l i = seat, ((loAt l).get i).1 = sh
  `k1FirstSeatsW`, `k1MaskSeatW`, `k1LaterSeatsW`
      BY LEAN's KERNEL, at the written lists: at link 0 member n is the opening's message n, for
      each message of the first written segment's first sending but the mask · the mask's written
      seat at link 0 is the seat of the opening's message of the mask's number · at each of the 25
      links the two members behind those of the first sending are message 0 of `placeL` l false,
      then of `placeL` l true
  `k1FirstSeatsW_can_fail`, `k1MaskSeatW_can_fail`, `k1LaterSeatsW_can_fail`
      CONTROLS THAT SAY NO: at the next member, at every n · at the opening's next message · with
      the link's two later sendings swapped, at both, at every link
  `first_seats_at_head`, `mask_seat_at_head`, `later_seats_at_head`
      UNDER THE HEAD AND THE OPENING: the member, its shape, its seat and the number, at P :=
      K1.firstPar Bs.G₀.first (K1.gpOf Zp) and the member number 2 | P := K1.parL Zp Bs.G₀ l d and
      the member number K1.noL l d

By. Another group of authors' (Honest/K1/Law/K1NumAtHead.lean): `seat_two_written`,
`seat_fifty_written`, `k1Num`; `parL_written` (Honest/K1/Law/FitsWritten.lean). Ours:
`segments_at_head` (PlacesWritten.lean of this folder), `par_at_head`
(Honest/K11/Plays/IndexKeyWritten.lean). Sealed: `AtMg.seats` (Johnson/P5T/CoreAtMg.lean): under the
head the plan's seats are the written ones. NEAR, the other authors', not called: `seat_two`,
`seat_fifty`, `k1Num_fifty` (K1NumAtHead.lean): the same seats against the list of all three chains'
seats.

WHAT IT IS NOT. Numbers and shapes of a public plan: nothing on what a table holds. THAT A WITNESS's
TABLE AT THAT NUMBER IS THE SENDER's ROWS IS NOT SAID HERE: that is the hinge `tab_rows`
(Honest/K1/ScriptTie.lean), under its own premises. The opening's fifth message, the index masks',
is no member of link 0's group. That the hypothesis on the public files can be met is not said.

Limits. SIX CLOSED FACTS BY EVALUATION IN LEAN's KERNEL; more of the other authors' beneath. The
full size and the format's second hash function alone. The head and the opening are premises. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.ProofFile.Honest.K1.Law.K1NumAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsWritten
import Johnson.Desc.ProofFile.Honest.K11.Plays.IndexKeyWritten
import Johnson.IMR.K10SeatFit
import Johnson.Desc.First.Close.Law.Drawn.Def
import Johnson.Desc.First.Close.Law.SeatsOfLink
import Johnson.Desc.First.Close.Law.MaskLaidFull
import Johnson.LPFE1R.RowPubAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (parGF placeL baseL3 seatOfMsg firstPar gpOf parL noL)
open VerifiableInference.Desc.First.Close (seatK10 seatsOfLink maskTree)
open VerifiableInference.Desc.LinkJoin (loAt)
open Johnson.Prover.Send (shapeAt)
open P5T (PSeat psFull)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **A PUBLIC TEST**: link l's member at position pos sits at seat and has the shape sh. -/
def k1SeatTie (ps : List PSeat) (l pos : Nat) (seat : Nat × Nat) (sh : OnBytes.OracleShape) :
    Bool :=
  match (VerifiableInference.Desc.First.Close.membersOf (loAt l))[pos]? with
  | some i =>
    (seatsOfLink ps l)[i.val]? == some seat &&
      decide (((loAt l).get i).1 = sh)
  | none => false

/-- What the test's yes gives. -/
theorem k1SeatTie_gives {ps : List PSeat} {l pos : Nat} {seat : Nat × Nat}
    {sh : OnBytes.OracleShape} (h : k1SeatTie ps l pos seat sh = true) :
    ∃ i, (VerifiableInference.Desc.First.Close.membersOf (loAt l))[pos]? = some i ∧
      ((loAt l).get i).1 = sh ∧
      seatK10 (loAt l) ps l i = seat := by
  unfold k1SeatTie at h
  split at h
  · rename_i i hi
    rw [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    refine ⟨i, hi, h.2, ?_⟩
    unfold seatK10
    rw [List.getD_eq_getElem?_getD, h.1]
    rfl
  · exact nomatch h

/-- The test at the first sending's messages but the mask. off: 0; a control lays 1. -/
def firstSeats (Sg : SegmentPub) (off : Nat) : List Bool :=
  (List.range ((Sg.sent.headD #[]).size - 1)).map fun n =>
    k1SeatTie psFull 0 (n + off) (seatOfMsg parGF 0 n) (shapeAt parGF n)

/-- The test at the two members behind those of the first sending. d: which of the link's two later
sendings stands at the q-th: (· == 1); a control lays (· == 0). -/
def laterSeats (l : Nat) (Sg : SegmentPub) (d : Nat → Bool) : List Bool :=
  (List.range 2).map fun q =>
    k1SeatTie psFull l ((Sg.sent.headD #[]).size - 1 + q)
      (seatOfMsg (placeL l (d q)) (baseL3 l (d q)) 0) (shapeAt (placeL l (d q)) 0)

set_option maxRecDepth 1000000 in
/-- **At link 0: member n is the opening's message n**, and there are some. -/
theorem k1FirstSeatsW : ((segsW.take 1).all fun Sg =>
    !(firstSeats Sg 0).isEmpty && (firstSeats Sg 0).all id) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- It can fail: at the next member it says no at every one. -/
theorem k1FirstSeatsW_can_fail :
    ((segsW.take 1).all fun Sg => (firstSeats Sg 1).all (!·)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **At link 0: the fresh mask's written seat is the seat of the opening's message of its
number.** -/
theorem k1MaskSeatW : ((segsW.take 1).all fun Sg =>
    decide ((maskTree 0, VerifiableInference.Desc.First.Close.maskPart 0) =
      seatOfMsg parGF 0 ((Sg.sent.headD #[]).size - 1))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- It can fail: at the opening's next message it says no. -/
theorem k1MaskSeatW_can_fail : ((segsW.take 1).all fun Sg =>
    !decide ((maskTree 0, VerifiableInference.Desc.First.Close.maskPart 0) =
      seatOfMsg parGF 0 ((Sg.sent.headD #[]).size - 1 + 1))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **At each link: the two members behind those of the first sending.** -/
theorem k1LaterSeatsW : (segsW.zipIdx.all fun x => decide (x.2 < 25) &&
    (laterSeats x.2 x.1 (· == 1)).all id) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- It can fail: with the two later sendings swapped it says no at both, at every link. -/
theorem k1LaterSeatsW_can_fail : (segsW.zipIdx.all fun x =>
    (laterSeats x.2 x.1 (· == 0)).all (!·)) = true := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **UNDER THE HEAD: the opening's message n, in front of the mask, is member n of link 0's
group, at its own seat and number.** -/
theorem first_seats_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[0]? = some Sg) {n : Nat}
    (hn : n < (Sg.sent.headD #[]).size - 1) :
    ∃ i, (VerifiableInference.Desc.First.Close.membersOf (loAt 0))[n]? = some i ∧
      ((loAt 0).get i).1 =
        shapeAt (firstPar Bs.G₀.first (gpOf Zp)) n ∧
      seatK10 (loAt 0) (P5J.At.pseats Zp) 0 i =
        K1.seatAtMember cF.blocksInOrder 2 (firstPar Bs.G₀.first (gpOf Zp)) n ∧
      P5J.At.arr Zp (seatK10 (loAt 0) (P5J.At.pseats Zp) 0 i).1
          (seatK10 (loAt 0) (P5J.At.pseats Zp) 0 i).2 =
        K1.k1Num Zp cF.blocksInOrder 2 (firstPar Bs.G₀.first (gpOf Zp)) n := by
  rw [segments_at_head h.toAtMg O] at hS
  have k := List.all_eq_true.1 k1FirstSeatsW Sg
    (List.mem_of_getElem? (i := 0) (by rw [List.getElem?_take_of_lt (by omega)]; exact hS))
  rw [Bool.and_eq_true] at k
  obtain ⟨i, hi, hsh, hk⟩ := k1SeatTie_gives
    (List.all_eq_true.1 k.2 _ (List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩))
  have hs : P5J.At.pseats Zp = psFull := h.toAtMg.seats
  have e : seatK10 (loAt 0) (P5J.At.pseats Zp) 0 i =
      K1.seatAtMember cF.blocksInOrder 2 (firstPar Bs.G₀.first (gpOf Zp)) n := by
    rw [hs, K1.seat_two_written h O n]
    exact hk
  refine ⟨i, hi, ?_, e, ?_⟩
  · rw [ProofFile.Honest.K11.par_at_head h O]
    exact hsh
  · rw [e]
    rfl

/-- **UNDER THE HEAD: the first segment's fresh mask sits at the seat of the opening's message of
its number.** -/
theorem mask_seat_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[0]? = some Sg) :
    (maskTree 0, VerifiableInference.Desc.First.Close.maskPart 0) =
        K1.seatAtMember cF.blocksInOrder 2 (firstPar Bs.G₀.first (gpOf Zp))
          ((Sg.sent.headD #[]).size - 1) ∧
      P5J.At.arr Zp (maskTree 0) (VerifiableInference.Desc.First.Close.maskPart 0) =
        K1.k1Num Zp cF.blocksInOrder 2 (firstPar Bs.G₀.first (gpOf Zp))
          ((Sg.sent.headD #[]).size - 1) := by
  rw [segments_at_head h.toAtMg O] at hS
  have k := of_decide_eq_true (List.all_eq_true.1 k1MaskSeatW Sg
    (List.mem_of_getElem? (i := 0) (by rw [List.getElem?_take_of_lt (by omega)]; exact hS)))
  have e : (maskTree 0, VerifiableInference.Desc.First.Close.maskPart 0) =
      K1.seatAtMember cF.blocksInOrder 2 (firstPar Bs.G₀.first (gpOf Zp))
        ((Sg.sent.headD #[]).size - 1) := by
    rw [K1.seat_two_written h O]
    exact k
  refine ⟨e, ?_⟩
  show P5J.At.arr Zp (maskTree 0, VerifiableInference.Desc.First.Close.maskPart 0).1
    (maskTree 0, VerifiableInference.Desc.First.Close.maskPart 0).2 = _
  rw [e]
  rfl

/-- **UNDER THE HEAD: behind the members of a link's first sending stand message 0 of its "reads",
then message 0 of its "digits", each at its own seat and number.** -/
theorem later_seats_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {l : Nat} {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[l]? = some Sg) {q : Nat}
    (hq : q < 2) :
    ∃ i, (VerifiableInference.Desc.First.Close.membersOf (loAt l))[
        (Sg.sent.headD #[]).size - 1 + q]? = some i ∧
      ((loAt l).get i).1 = shapeAt (parL Zp Bs.G₀ l (q == 1)) 0 ∧
      seatK10 (loAt l) (P5J.At.pseats Zp) l i =
        K1.seatAtMember cF.blocksInOrder (noL l (q == 1)) (parL Zp Bs.G₀ l (q == 1)) 0 ∧
      P5J.At.arr Zp (seatK10 (loAt l) (P5J.At.pseats Zp) l i).1
          (seatK10 (loAt l) (P5J.At.pseats Zp) l i).2 =
        K1.k1Num Zp cF.blocksInOrder (noL l (q == 1)) (parL Zp Bs.G₀ l (q == 1)) 0 := by
  rw [segments_at_head h.toAtMg O] at hS
  have k := List.all_eq_true.1 k1LaterSeatsW (Sg, l) (List.mem_zipIdx_iff_getElem?.2 hS)
  rw [Bool.and_eq_true, decide_eq_true_eq] at k
  have hl : l < 25 := k.1
  obtain ⟨i, hi, hsh, hk⟩ := k1SeatTie_gives
    (List.all_eq_true.1 k.2 _ (List.mem_map.2 ⟨q, List.mem_range.2 hq, rfl⟩))
  have hs : P5J.At.pseats Zp = psFull := h.toAtMg.seats
  have e : seatK10 (loAt l) (P5J.At.pseats Zp) l i =
      K1.seatAtMember cF.blocksInOrder (noL l (q == 1)) (parL Zp Bs.G₀ l (q == 1)) 0 := by
    rw [hs, K1.seat_fifty_written h O hl (q == 1) 0]
    exact hk
  refine ⟨i, hi, ?_, e, ?_⟩
  · rw [K1.parL_written h O l (q == 1)]
    exact hsh
  · rw [e]
    rfl

end ProofFile.Honest.K2.Law

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.Law.k1SeatTie
#print axioms ProofFile.Honest.K2.Law.k1SeatTie_gives
#print axioms ProofFile.Honest.K2.Law.firstSeats
#print axioms ProofFile.Honest.K2.Law.laterSeats
#print axioms ProofFile.Honest.K2.Law.k1FirstSeatsW
#print axioms ProofFile.Honest.K2.Law.k1FirstSeatsW_can_fail
#print axioms ProofFile.Honest.K2.Law.k1MaskSeatW
#print axioms ProofFile.Honest.K2.Law.k1MaskSeatW_can_fail
#print axioms ProofFile.Honest.K2.Law.k1LaterSeatsW
#print axioms ProofFile.Honest.K2.Law.k1LaterSeatsW_can_fail
#print axioms ProofFile.Honest.K2.Law.first_seats_at_head
#print axioms ProofFile.Honest.K2.Law.mask_seat_at_head
#print axioms ProofFile.Honest.K2.Law.later_seats_at_head
