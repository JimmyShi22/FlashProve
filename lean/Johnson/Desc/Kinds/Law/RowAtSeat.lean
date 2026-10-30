-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/RowAtSeat.lean: THE OUTPUT HEAD's ROW OF THE TABLE OF JOINTS, WITH THE 17 ROW FORMS (idn · the two sums · keys and rider in our own words; planes on neither side; join not among the outs), FROM THE DECISION OF THE BLOCK AT THE FIRST CHAIN's OWN CARRIED RECORD
(Johnson/Stored/HeadSeatAt.lean: blockAt h iU3 work l, over seatAt h iU3 and parOf h work): WITH NO PREMISE ON THE SEAT: STATED AND PROVED:
Law/RowK6.lean's law at that seat, its premise SeatBack paid by seatBack_at (Law/HeardBack.lean).
WHAT IT DOES NOT SAY. c AND mask ARE LETTERS UNDER "FOR ALL", TIED HERE TO NOTHING THAT IS FIXED IN FRONT OF THE DRAWS: the law is meant to be spent at the
witness's components that are pinned in front of the block's first draw (the table of joints: pin 4 0, pinW): THAT INSTANCE IS THE CALLER's, AND IS NOWHERE; whoever
may pick mask behind the draws makes every hidden scalar what they like. At parOf, before := []: the block's own test that the messages with the cells precede its first draw is idle at this seat. rs IS WHAT decide IS SHOWN (no sealed digest): that these are the rounds of the written reading is another file's equation (Johnson/Desc/Sound/ShownRounds.lean).
That the 35 forms are 0 and the claim on the weights true (Opened: what the block opens: later blocks'
laws). How probable a bad draw is: no written challenge is counted; no sum of errors is taken. That the record's ledger is
WellLaid, that the heard token is below V, that the plan has a feature (0 < d): premises. That an honest run meets the
premises: not shown.
Whether a description seats a block over this very seat: not here.
  seatBack_iff       SeatBack (RowAtDecide.lean) is SeatBackHeard (HeardBack.lean), to the letter.
  RowAtSeatStatement the decision of blockAt h iU3 work l goes on from s to s' · WellLaid · the tests on the plan and the
                     request · 0 < d · y < V · the rounds canonical · Sound.NoBad (ruleK6 …): Opened at s' gives ClosedWhole at s'.
IMPORTED: Law/HeardBack.lean; Johnson/Stored/HeadSeatAt.lean.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RowK6
import Johnson.Desc.Kinds.Law.HeardBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open VerifiableInference.Desc.First (S)

/-- **K6's ROW AT THE REAL SEAT.** -/
def RowAtSeatStatement : Prop :=
  ∀ (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) (s : S) (c : NCells)
    (mask : Nat → E) (s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    (blockAt h iU3 work l).decide s rs gs = .ok s' → WellLaid ((seatAt h iU3).ledger s) →
    (parOf h work).ok = true → hasFeatures (parOf h work) →
    (parOf h work).okStart ((seatAt h iU3).request s) = true →
    (∀ y, Reply.token (seatAt h iU3).toSeat s = some y → y < (parOf h work).sizes.V) →
    Canonical rs → Sound.NoBad (ruleK6 (parOf h work) (seatAt h iU3) s c mask) rs →
    Opened (parOf h work) (seatAt h iU3) s' c mask →
    ClosedWhole (parOf h work) (seatAt h iU3) s' c mask

namespace Came

theorem seatBack_iff {S : Type} (p : Par) (L : Seat S) (s : S) :
    SeatBack p L s ↔ SeatBackHeard p L s := Iff.rfl

theorem rowAtSeat : RowAtSeatStatement := by
  intro h iU3 work l s c mask s' rs gs hd hWL hplan hd0 hreq hy hcan hnb hopen
  exact rowK6 S Unit (fun _ => ()) (seatAt h iU3) l 4 (parOf h work) s c mask s' rs gs hd
    ((seatBack_iff _ _ _).2 (seatBack_at h iU3 work s)) hWL hplan hd0 hreq hy hcan hnb hopen

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rowAtSeat
