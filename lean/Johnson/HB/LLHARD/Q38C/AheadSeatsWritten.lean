-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/Q38C/AheadSeatsWritten.lean: the seat equation for the oracle messages that are
still ahead (`aheadSeatsB`, Johnson/HB/LLHARD/Q38C/AheadSeats.lean) AT THE WRITTEN VALUES OF THE
FULL SIZE, at all 25 segments. Definitions and five statements, each by an evaluation in Lean's
kernel (`decide +kernel`).

THE ARGUMENTS, EACH WITH ITS WRITTEN TERM: the request's shape · `shapeFull`
(Johnson/Desc/ReqLit/Full.lean) · the numbers' "sent" and "group" · `N0Full`'s · the lookups' seat
of a segment's own message · `P6T.seatT psFull l` (Johnson/P5T/SeatsAt.lean over
Johnson/P5T/PlanSeatsFull.lean) · the messages sent already · `c_n0Full l`: 4 | 2. The ties under
the head: Johnson/HB/LLHARD/Q38C/AheadSeatsAtHead.lean.

  `c_n0Full`, `c_atFull`, `c_shape0`: helpers.
  `aheadSeats_written`: (W).
  `aheadSeats_walks`: at each segment just one message is ahead, of moment 2.
  `c_seat_there`: at that message the lookups' seat is found in the list of seats: `P6T.seatT`
    answers (0, 0) in silence where it finds none: that default is not met here. And each of the 25
    segments has one seat in its sending of moment 2; number 25 has none.
  `aheadSeats_rejects`, `c_rejects_more`: (N): six bent forms, each rejected at EACH of the 25.

WHAT THE BENT FORMS SHOW, AND WHAT NOT. Every seat's tree moved by 1000, every tenant by 1, every
moment laid to 0: once (W) and `aheadSeats_walks` hold these cannot be accepted, by logic alone:
they show that the test reads the seat and the moment, no more. No seat may be read: it shows that
the third clause is read; at moment 2 that clause follows from the second, as "group" holds all
three sendings. THE FORMS THAT TRY THE SEAT EQUATION ITSELF lay another segment's sendings under an
unturned seat: the next segment's (at segment 24 it rejects for want of a list: `c_seat_there`), and
the next segment's going round from 24 to 0 (at each of the 25 another seat stands there). NOT TRIED
AT ANY VALUE BUT ONE: the place in the sending: as each segment has one message of moment 2, it is 0
at all 25.

WHICH ROWS OF THE HEAD IT SPENDS, BY THE CODE: none: it reads no field of the head.

Limits. The full size alone. Nothing on soundness.
-/
import Johnson.HB.LLHARD.Q38C.AheadSeats
import Johnson.P5T.PlanSeatsFull
import Johnson.P5T.SeatsAt
import Johnson.Desc.ReqLit.Full

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Q38
open P5T (psFull N0Full)
open VerifiableInference.Desc.ReqLit (shapeFull)

/-- How many oracle messages of segment l are of the moments 0 and 1, at the full size: 4 at a
feed-forward segment, 2 at an attention segment and at the output head's. -/
def c_n0Full (l : ℕ) : ℕ := if l % 2 == 0 && l != 24 then 4 else 2

/-- The test at segment l, at the written values, at a function on seats laid over the written
one. -/
def c_atFull (f : ℕ × ℕ → ℕ × ℕ) (l : ℕ) : Bool :=
  aheadSeatsB shapeFull (N0Full.sent l) (N0Full.group l) (fun j => f (P6T.seatT psFull l j)) l
    (c_n0Full l)

set_option maxRecDepth 1000000 in
/-- **(W)** At the written values the test accepts at all 25 segments. -/
theorem aheadSeats_written : (List.range 25).all (c_atFull id) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **(N)** It rejects at each of the 25: with every seat's tree moved by 1000; with every seat's
tenant moved by 1; where no seat may be read; at the next segment's sendings. -/
theorem aheadSeats_rejects :
    ((List.range 25).any (c_atFull fun x => (x.1 + 1000, x.2)),
      (List.range 25).any (c_atFull fun x => (x.1, x.2 + 1)),
      (List.range 25).any (fun l => aheadSeatsB shapeFull (N0Full.sent l) []
        (P6T.seatT psFull l) l (c_n0Full l)),
      (List.range 25).any (fun l => aheadSeatsB shapeFull (N0Full.sent (l + 1)) (N0Full.group l)
        (P6T.seatT psFull l) l (c_n0Full l))) = (false, false, false, false) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **It does not accept for want of members**: at each of the 25 segments just one oracle message
is ahead, and it is of moment 2. -/
theorem aheadSeats_walks :
    (List.range 25).map (fun l => ((shapeFull.link[l]?).map fun sh =>
      (sh.messages.drop (c_n0Full l)).map (·.moment)).getD []) = List.replicate 25 [2] := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At the message that is ahead the lookups' seat is found in the list of seats, at each of the 25;
and how many seats each segment's sending of moment 2 has. -/
theorem c_seat_there :
    ((List.range 25).all (fun l => (P6T.ownAt psFull l (c_n0Full l)).isSome),
      (List.range 26).map (fun l => (N0Full.sent l 2).length)) =
      (true, List.replicate 25 1 ++ [0]) := by decide +kernel

/-- The written shape with every oracle message's moment laid to 0. -/
def c_shape0 : OnBytes.Params.ReqShape :=
  { shapeFull with
    link := shapeFull.link.map fun sh =>
      { sh with messages := sh.messages.map fun M => { M with moment := 0 } } }

set_option maxRecDepth 1000000 in
/-- **(N)** It rejects at each of the 25: at the next segment's sendings, going round from 24 to 0;
and at the shape with every moment laid to 0. -/
theorem c_rejects_more :
    ((List.range 25).any (fun l => aheadSeatsB shapeFull (N0Full.sent ((l + 1) % 25))
        (N0Full.group l) (P6T.seatT psFull l) l (c_n0Full l)),
      (List.range 25).any (fun l => aheadSeatsB c_shape0 (N0Full.sent l) (N0Full.group l)
        (P6T.seatT psFull l) l (c_n0Full l))) = (false, false) := by decide +kernel

end Q38

#print axioms Q38.aheadSeats_written
#print axioms Q38.aheadSeats_rejects
#print axioms Q38.aheadSeats_walks
#print axioms Q38.c_seat_there
#print axioms Q38.c_rejects_more
