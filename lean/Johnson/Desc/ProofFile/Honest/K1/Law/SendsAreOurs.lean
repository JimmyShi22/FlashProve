-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/SendsAreOurs.lean: THE SHARED "SENDING" (the kind K1): EVERY
SEAT OF THE PLAN's LIST (all three chains') THAT STANDS IN ONE OF K1's 52 SENDINGS IS THE SEAT OF A
MESSAGE OF K1's OWN PLAN THERE: under the library's head, a member q of P5J.At.pseatsAll Zp whose
sending's number is 0, or 3 * l + momL d at a link l below 25, or 81, has its place q.idx below the
plan's number of messages, and (q.j, q.t) is our seat of message number q.idx at that member. THE
OTHER WAY ROUND FROM seat_two, seat_fifty, seat_w (K1NumAtHead.lean, K1NumAtW.lean), which go from
our seat to the sending and the place. PUBLIC DATA ALONE: plans, the plan's list of seats, numbers:
WHICH MESSAGE SITS WHERE, NEVER WHAT STANDS IN IT. Nine theorems; no definition.
NO PROPERTY IS CLAIMED.

  CLOSED FACTS, evaluated in Lean's kernel at the written list, EACH WITH A TWIN THAT SAYS NO:
  - sendW2, sendW50, sendW356: each member of the written list in that sending has its place below
    the written plan's number of messages and sits at the written plan's seat of that message.
  - sendW2_bites, sendW50_bites, sendW356_bites: one tree further the test says no.
  UNDER h (the library's head: A HYPOTHESIS) AND O:
  - sendIsOurs_two, sendIsOurs_fifty, sendIsOurs_w: the same at the plan's own list and at our
    seats seatAtMember.

Kin, told. backW2, backW50 (K1NumAtHead.lean) and backW356 (K1NumAtW.lean) say, for each n BELOW the
plan's number of messages, that the written list has just one member number n of the sending, at our
seat. NEW HERE: that the sending has no member at or beyond that number; and the form by the member.
THE CONVERSE, ALSO BY THE MEMBER: k1Seat_alone_two and k1Seat_alone_fifty (K1SeatAlone.lean) and
k1Seat_alone_w (K1NumOthersW.lean): a member of the plan's list at our seat has that sending's
number and that place. k1_seat_far (AgreeFar.lean): no seat of a far sending sits at a seat of ours.

For whom. A joined Script's test asks that each declared seat has its lots. With
AtFullSide/K1/DeclaredSeatsAtHead.lean (each declared seat is (q.j, q.t) of some member q of the
plan's list): where such a q stands in one of K1's sendings, the declared seat is the seat of one of
K1's messages. THAT JOIN IS NOT TYPED HERE: no lot and no Script is named.

Limits. THE FULL SIZE ALONE; the format's second hash function alone. THE CLOSED FACTS SPEAK OF THE WRITTEN
LIST; the head carries them to the plan's (pseatsAll_written). That 0, the fifty numbers and 81 are
all of K1's sendings is not said here. Nothing on a run, or on what any coin is. Nothing on any
property.
Whoever calls one of the last three in front of a law over coins names h and O beside it: they are
premises, paid nowhere here.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.K1NumAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (parGF parWF seatOfMsg placeL baseL3 momL fiftyB fifty_of)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open P5T (PSeat seatsAllFull)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)

/-! ## 1 The closed facts -/

set_option maxRecDepth 1000000 in
/-- Each member of the written list in sending number 0 sits at the opening's seat of its place. -/
theorem sendW2 : (seatsAllFull.all fun q => q.send != 0 ||
    (decide (q.idx < parGF.sent.size) && decide ((q.j, q.t) = seatOfMsg parGF 0 q.idx))) =
      true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: one tree further the test says no. -/
theorem sendW2_bites : (seatsAllFull.all fun q => q.send != 0 ||
    (decide (q.idx < parGF.sent.size) && decide ((q.j, q.t) = seatOfMsg parGF 1 q.idx))) =
      false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The like at each of the fifty. -/
theorem sendW50 : fiftyB (fun l d => seatsAllFull.all fun q => q.send != 3 * l + momL d ||
    (decide (q.idx < (placeL l d).sent.size) &&
      decide ((q.j, q.t) = seatOfMsg (placeL l d) (baseL3 l d) q.idx))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: AT EACH OF THE FIFTY, one tree further, the test says no. -/
theorem sendW50_bites : fiftyB (fun l d => !(seatsAllFull.all fun q => q.send != 3 * l + momL d ||
    (decide (q.idx < (placeL l d).sent.size) &&
      decide ((q.j, q.t) = seatOfMsg (placeL l d) (baseL3 l d + 1) q.idx)))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The like at sending number 81, where the request's own table is sent. -/
theorem sendW356 : (seatsAllFull.all fun q => q.send != 81 ||
    (decide (q.idx < parWF.sent.size) && decide ((q.j, q.t) = seatOfMsg parWF 82 q.idx))) =
      true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: one tree further the test says no. -/
theorem sendW356_bites : (seatsAllFull.all fun q => q.send != 81 ||
    (decide (q.idx < parWF.sent.size) && decide ((q.j, q.t) = seatOfMsg parWF 83 q.idx))) =
      false := by
  decide +kernel

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- h, O, hq AND hs ARE PREMISES. **A SEAT OF THE PLAN's LIST IN SENDING NUMBER 0 IS THE OPENING's
SEAT OF ITS PLACE.** -/
theorem sendIsOurs_two (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {q : PSeat}
    (hq : q ∈ P5J.At.pseatsAll Zp) (hs : q.send = 0) :
    q.idx < (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size ∧
      (q.j, q.t) = seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) q.idx := by
  rw [pseatsAll_written h] at hq
  rw [seat_two_written h O q.idx, K1.eG_atAll h O (K1.pin1_atAll h)]
  have c := List.all_eq_true.1 sendW2 q hq
  rw [Bool.or_eq_true] at c
  rcases c with c | c
  · rw [hs] at c
    simp at c
  · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at c
    exact c

/-- h, O, hl, hq AND hs ARE PREMISES. **THE LIKE AT EACH OF THE FIFTY.** -/
theorem sendIsOurs_fifty (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {l : ℕ} (hl : l < 25) (d : Bool) {q : PSeat}
    (hq : q ∈ P5J.At.pseatsAll Zp) (hs : q.send = 3 * l + momL d) :
    q.idx < (K1.parL Zp Bs.G₀ l d).sent.size ∧
      (q.j, q.t) = seatAtMember cF.blocksInOrder (K1.noL l d) (K1.parL Zp Bs.G₀ l d) q.idx := by
  rw [pseatsAll_written h] at hq
  rw [seat_fifty_written h O hl d q.idx, parL_written h O l d]
  have c := List.all_eq_true.1 (fifty_of sendW50 l hl d) q hq
  rw [Bool.or_eq_true] at c
  rcases c with c | c
  · rw [hs] at c
    simp at c
  · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at c
    exact c

/-- h, O, hq AND hs ARE PREMISES. **THE LIKE AT SENDING NUMBER 81.** -/
theorem sendIsOurs_w (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {q : PSeat}
    (hq : q ∈ P5J.At.pseatsAll Zp) (hs : q.send = 81) :
    q.idx < (K1.parW Zp.first (wGp Zp) 4 wMsgFull).sent.size ∧
      (q.j, q.t) = seatAtMember cF.blocksInOrder 356 (K1.parW Zp.first (wGp Zp) 4 wMsgFull) q.idx := by
  rw [pseatsAll_written h] at hq
  rw [seat_w_written h O q.idx, parW_written h O]
  have c := List.all_eq_true.1 sendW356 q hq
  rw [Bool.or_eq_true] at c
  rcases c with c | c
  · rw [hs] at c
    simp at c
  · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at c
    exact c

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.sendW2
#print axioms ProofFile.Honest.K1.sendW2_bites
#print axioms ProofFile.Honest.K1.sendW50
#print axioms ProofFile.Honest.K1.sendW50_bites
#print axioms ProofFile.Honest.K1.sendW356
#print axioms ProofFile.Honest.K1.sendW356_bites
#print axioms ProofFile.Honest.K1.sendIsOurs_two
#print axioms ProofFile.Honest.K1.sendIsOurs_fifty
#print axioms ProofFile.Honest.K1.sendIsOurs_w
