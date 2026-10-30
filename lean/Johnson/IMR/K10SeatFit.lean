-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/K10SeatFit.lean: FOR THE CLOSING KIND K10's
PREMISE ON WHAT STANDS BEHIND THE CLOSING (hCar), NUMBER (7) OF ITS LIST OF CLOSED FACTS ON
THE PLAN: "THE SEAT FITS" (SeatFitAt, Johnson/Top/H0/K2Caller/KeptSeatOf.lean) AT EVERY MEMBER OF A
LINK's WRITTEN LIST, NOT THE KEPT ALONE, AT ALL 25 LINKS, UNDER THE ONE HEAD P5J.AtMg. For M3. A
test with code, its law, the test at the written values by the kernel, and the sentence under the
head.

WHAT IT IS NOT, FIRST. A member of the head is proved at storedPublicFiles and zGap alone (at secondHashFunction, with
fixedConfigurationDigest in the digest's place; side library AtFullSide/Top/); so what rests on the head counts as
proved there alone. AT LINK 0 IT STANDS AT THE SIX
(the written list with the index masks' message), NOT at the five-list loFive | seatFive. The full
size alone. It says nothing of (6) and (8) of that list. No soundness.

  coverB ps lo seats   each place i of lo has, among the plan's entries with a sample, one with lo's
                    shape at i and the seat seats[i]
  seatFit_of_cover  THE LAW, general: the head's named test seatsFitP and a yes of coverB give
                    SeatFitAt at every place of lo, at seat i := seats.getD i (0, 0)
  cover_written     BY THE KERNEL: coverB says yes at the written entries, link l's written list and
                    its seats off the plan, at all 25
  cover_can_fail    A NEGATIVE LINE: link 1's list against link 2's seats: no
  **seatFit_at_head**   under the head, at l < 25: SeatFitAt (F0T o Zp Np cF) (At.cs Zp) (loAt l)
                    (seatK10 (loAt l) (At.pseats Zp) l) i, at every i. At every o : ProofFile.SecondHashFunctionArgument.

WHY NO NEW TEST IS NEEDED. The head's own field plan.fit says "no fault" at every entry of the plan
with a sample; under the head the plan's entries are the written ones (P5J.AtMg.seats).
CALLED: fit_at (Johnson/Top/H0/K2Caller/SeatFitsPlan.lean), seatFitOne_of_noFault (SeatFitsB.lean
beside it), P5J.AtMg.seats (Johnson/P5T/CoreAtMg.lean). THE LETTERS: loAt
(Johnson/LPFE1R/RowPubAt.lean), seatsOfLink and seatK10
(Johnson/Desc/First/Close/Law/SeatsOfLink.lean).
KIN. seatFitOne_kept and seatFits_new (SeatFitsPlan.lean) go the same road at the kept members and
at the list that a switch sends, in the table's numbers' letters.

-/
import Johnson.Top.H0.K2Caller.SeatFitsPlan
import Johnson.Top.H0.K2Caller.KeptSeatOf
import Johnson.Desc.First.Close.Law.SeatsOfLink
import Johnson.LPFE1R.RowPubAt
import Johnson.P5T.CoreAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM.K10

open OnBytes
open VerifiableInference.Desc (Chain FileDescription)
open VerifiableInference.Desc.First.K2Caller (SeatFitAt seatFitOne_of_noFault fit_at)
open VerifiableInference.Desc.First.Close (seatsOfLink seatK10)
open VerifiableInference.Desc.LinkJoin (loAt)
open OnBytes.Maker (WholeD)
open P5J

/-- Each place of lo has an entry with a sample of its shape at its seat. -/
def coverB (ps : List P5T.PSeat) (lo : List (OracleShape × ℕ)) (seats : List (ℕ × ℕ)) : Bool :=
  (List.range lo.length).all fun i =>
    (ps.filter (·.smpd)).any fun p =>
      decide (p.shape = (lo.getD i default).1) && decide (p.seat = seats.getD i (0, 0))

/-- **THE LAW.** -/
theorem seatFit_of_cover {Xi : Type} (G : FileDescription Xi) (cs : Codes) (ps : List P5T.PSeat)
    (hF : P5T.seatsFitP G cs ps = true) (lo : List (OracleShape × ℕ)) (seats : List (ℕ × ℕ))
    (hc : coverB ps lo seats = true) (i : Fin lo.length) :
    SeatFitAt G cs lo (fun i => seats.getD i.val (0, 0)) i := by
  obtain ⟨p, hp, hb⟩ := List.any_eq_true.1
    (List.all_eq_true.1 hc i.val (List.mem_range.2 i.isLt))
  obtain ⟨hp1, hp2⟩ := List.mem_filter.1 hp
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  have e1 : (lo.get i).1 = p.shape := by
    rw [hb.1, List.getD_eq_getElem _ _ i.isLt]
    rfl
  have hn : VerifiableInference.Desc.seatFaultAt G cs "" (lo.get i).1 (seats.getD i.val (0, 0)).1
      (seats.getD i.val (0, 0)).2 = none := by
    rw [e1, ← hb.2]
    exact fit_at G cs hF hp1 hp2
  have key := seatFitOne_of_noFault G cs lo (fun i => seats.getD i.val (0, 0)) i hn
  unfold VerifiableInference.Desc.First.K2Caller.SeatFitOne at key
  unfold SeatFitAt
  exact key

set_option maxRecDepth 1000000 in
/-- **BY THE KERNEL, AT ALL 25.** -/
theorem cover_written : (List.range 25).all (fun l =>
    coverB P5T.psFull (loAt l) (seatsOfLink P5T.psFull l)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative line: link 1's list against link 2's seats. -/
theorem cover_can_fail : coverB P5T.psFull (loAt 1) (seatsOfLink P5T.psFull 2) = false := by
  decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **(7), under the head.** -/
theorem seatFit_at_head (h : AtMg o Z D r Zp Np cF) {l : ℕ} (hl : l < 25)
    (i : Fin (loAt l).length) :
    SeatFitAt (F0T o Zp Np cF) (At.cs Zp) (loAt l) (seatK10 (loAt l) (At.pseats Zp) l) i := by
  have hs : At.pseats Zp = P5T.psFull := h.seats
  exact seatFit_of_cover _ _ _ h.plan.fit (loAt l) (seatsOfLink (At.pseats Zp) l)
    (by rw [hs]; exact List.all_eq_true.1 cover_written l (List.mem_range.2 hl)) i

end IM.K10

#print axioms IM.K10.seatFit_of_cover
#print axioms IM.K10.cover_written
#print axioms IM.K10.cover_can_fail
#print axioms IM.K10.seatFit_at_head
