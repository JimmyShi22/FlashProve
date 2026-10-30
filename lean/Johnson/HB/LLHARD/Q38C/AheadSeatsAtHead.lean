-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/Q38C/AheadSeatsAtHead.lean: THE SEAT EQUATION FOR THE ORACLE MESSAGES THAT ARE
STILL AHEAD (`aheadSeatsB`, Johnson/HB/LLHARD/Q38C/AheadSeats.lean) UNDER THE HEAD, at each of the
25 segments. No premise beside the head (`AtMg`, Johnson/P5J/AtMg.lean) and l ≤ 24; at every
function o in the place of the second hash function. Statements with their proofs.

WHICH ROWS OF THE HEAD IT SPENDS, BY THE CODE: ROWS 1 AND 9 of the thirteen-row list of the proof
file's entry tests (Johnson/Desc/Laid/ProofAsks.lean). The head holds that every entry test accepts.
Row 9 compares the planner's sizes, lists and sendings with written values: `c_shape_at_head` spends
it by `AtMg.pins` (Johnson/P5T/FenceAtMg.lean; its first half), and so do
`AtMg.seats` and `AtMg.N_six` (Johnson/P5T/CoreAtMg.lean), which `aheadSeats_at_head` calls. These
two spend row 1 too, the comparison of the declared rounds with the written ones, through "the value
is laid". Over the eight-row list row 9 is not there, and nothing here can be had. The statements
hold under the head BECAUSE these rows compare with the written values: they are no facts on what
the makers make of given public files.

THE ARGUMENTS, EACH WITH ITS TIE: the shape · `c_shape_at_head` · the numbers' "sent" and "group" ·
`AtMg.N_six` · the lookups' seats · `AtMg.seats` · the messages sent already · `c_n0_at_head`.

  `c_n0_written`, `c_n0_rejects`: a closed fact and its negative test, by evaluations in Lean's
    kernel (`decide +kernel`).
  `c_shape_at_head`, `c_n0_at_head`: ties.
  `aheadSeats_at_head`: **(Z)**.

Limits. The full size alone. That a head can be had at given public files is not said. Nothing on
soundness.
-/
import Johnson.HB.LLHARD.Q38C.AheadSeatsWritten
import Johnson.P5T.CoreAtMg
import Johnson.P5J.Rad3Seat3At
import Johnson.P1K8R.FoldAtDraw
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Goal.Numbers.RequestWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Q38
open OnBytes.Maker (WholeD)
open P5T (psFull N0Full)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.PlanWritten (pinnedAt_of_row request_shape_written)
open VerifiableInference.PlanWritten.Joined (first_written_in_scope)

set_option maxRecDepth 1000000 in
/-- At the written shape, how many oracle messages of a segment are of the moments 0 and 1. -/
theorem c_n0_written :
    (List.range 25).all (fun l =>
      Meaning.K2.msgsAt shapeFull l 0 + Meaning.K2.msgsAt shapeFull l 1 == c_n0Full l) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: with moment 2 counted too, the number is another at each of the 25. -/
theorem c_n0_rejects :
    (List.range 25).any (fun l =>
      Meaning.K2.msgsAt shapeFull l 0 + Meaning.K2.msgsAt shapeFull l 1 +
        Meaning.K2.msgsAt shapeFull l 2 == c_n0Full l) = false := by decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- The request's shape, as read back, is the written one. -/
theorem c_shape_at_head (h : P5J.AtMg o Z D r Zp Np cF) : Zp.first.shape = shapeFull :=
  (first_written_in_scope h.scope h.laid.pub
    (pinnedAt_of_row (by rw [h.pins.1, Bool.or_true]))).2.2.1.trans request_shape_written

/-- The number of a segment's oracle messages that are sent in front of the draw. -/
theorem c_n0_at_head (h : P5J.AtMg o Z D r Zp Np cF) {l : ℕ} (hl : l ≤ 24) :
    P1K8T.n0At Zp l = c_n0Full l := by
  unfold P1K8T.n0At
  rw [c_shape_at_head h]
  exact eq_of_beq (List.all_eq_true.1 c_n0_written l (List.mem_range.2 (by omega)))

/-- **(Z) UNDER THE HEAD THE SEAT EQUATION ACCEPTS AT EACH OF THE 25 SEGMENTS**, at the head's own
shape, numbers and lookups' seats, and at the number of messages that are sent in front of the
approximate range proof's draw. -/
theorem aheadSeats_at_head (h : P5J.AtMg o Z D r Zp Np cF) {l : ℕ} (hl : l ≤ 24) :
    aheadSeatsB Zp.first.shape ((P5J.At.N Zp cF).sent l) ((P5J.At.N Zp cF).group l)
      (P5J.At.seat3At Zp l true) l (P1K8T.n0At Zp l) = true := by
  have eN : (P5J.At.N Zp cF).sent = N0Full.sent := h.N_six.1
  have eg : (P5J.At.N Zp cF).group l = N0Full.group l := by
    unfold VerifiableInference.Desc.First.Numbers.group
    rw [eN]
  have ep : P5J.At.pseats Zp = psFull := h.seats
  have es : P5J.At.seat3At Zp l true = fun j => P6T.seatT psFull l j := by
    rw [← ep]
    rfl
  rw [c_shape_at_head h, eN, eg, es, c_n0_at_head h hl]
  exact List.all_eq_true.1 aheadSeats_written l (List.mem_range.2 (by omega))

end Q38

#print axioms Q38.c_n0_written
#print axioms Q38.c_n0_rejects
#print axioms Q38.c_shape_at_head
#print axioms Q38.c_n0_at_head
#print axioms Q38.aheadSeats_at_head
