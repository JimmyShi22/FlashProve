-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/IMR/K10PlanClosed.lean: FOR THE CLOSING KIND K10's PREMISE ON WHAT STANDS BEHIND THE
CLOSING (hCar), NUMBER (8) OF ITS FILES' LIST OF CLOSED FACTS ON THE PLAN: THE PART OF planPubB THAT
READS NO STATE (planClosedB, Johnson/Desc/First/Link/Law/PlanClosedB.lean) SAYS TRUE AT EVERY MEMBER
OF A LINK's WRITTEN LIST, AT ALL 25 LINKS, AND AT LINK 0's FIVE-LIST, UNDER THE ONE HEAD P5J.AtMg.


WHAT IT IS NOT, FIRST. planClosedO BELOW IS A SECOND TEXT OF planClosedB: that file's own lines,
with a letter d? where they say G.oracleAt seat.1: TIED BY rfl (planClosedB_is): if that file's
text changes, Lean breaks the tie at once: the two cannot drift apart unseen. Why: a line for the
kernel needs a closed term; planClosedB takes a whole description G, and of G it reads that one
value. (The form of Johnson/P5T/SeatsFitWritten.lean's seatFaultO.) NOT planPubB WHOLE: its first
clause reads the state (o < t.book.place.size): not here. A member of the head is proved at storedPublicFiles
and zGap alone (at secondHashFunction, with fixedConfigurationDigest in the digest's place; side library AtFullSide/Top/); so what
rests on the head counts as proved there alone. The full size alone. No soundness.

  planClosedO · planClosedB_is   the second text; the tie
  oracleAt_of_cut   where the first chain's cut is the written one, what the description tells of a
                    tree below 83 is the written telling
  closedLinkB os l l'   at every member i of link l's written list: its seat's tree is below 83; os
                    tells that tree; planClosedO at that telling, the written plan's list LFull, the
                    member's number read at link l', its seat, and its shape's length
  closedFiveB os    the same at loFive, noFive, seatFive
  closed_written · closed_five   BY THE KERNEL: yes at the written tellings, at all 25; at the five
  closed_can_fail   A NEGATIVE LINE: with each tree handed its neighbour's telling not all 25 pass
  closed_can_fail_no   A NEGATIVE LINE: with the numbers read at the next link no link passes
  **planClosed_at_head · planClosed_five_at_head**   under the head, for the Ld that laidAtCodes
                    returns at the public part's own codes and sendings. At every o : ProofFile.SecondHashFunctionArgument.
AGAINST AN IDLE YES. planClosedB says true where the description tells nothing of the seat's tree.
The kernel's lines hold also that the tree IS told.
CALLED: ld_at_laid (Johnson/LPFE1R/SeedPublicFull.lean), P5J.AtMg.seats, P5J.AtMg.codes_full
(Johnson/P5J/CodesFullAtMg.lean), P5J.pins_of_laid, told_at_written, oraclesOf_told, cut_tells.
KIN. oracleAt_of_cut's four lines stand inside the proof of P5T.seatsFit_of_cut.

-/
import Johnson.Desc.First.Link.Law.PlanClosedB
import Johnson.LPFE1R.SeedPublicFull
import Johnson.LPFE1R.RowPubAt
import Johnson.Desc.First.Close.Law.FiveAtFull
import Johnson.P5T.SeatsFitWritten
import Johnson.P5J.CodesFullAtMg
import Johnson.P5T.CoreAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM.K10

open OnBytes
open Johnson.G (codesFull2)
open Johnson.Pack (aOf)
open VerifiableInference.Desc (Chain FileDescription oraclesOf)
open VerifiableInference.Desc.LinkJoin (planClosedB loAt seatsFullW ld_at_laid)
open VerifiableInference.Desc.First (toldCut told_at_written)
open VerifiableInference.Desc.First.Close (noK10 seatK10 loFive seatFive noFive)
open VerifiableInference.Desc.K12.Door (laidAtCodes)
open VerifiableInference.Desc.K13.Law (LFull oraclesOf_told cut_tells)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open OnBytes.Maker (WholeD)
open P5J

/-- planClosedB's own text, at what is told of the seat's tree. -/
def planClosedO (d? : Option VerifiableInference.Desc.Oracle)
    (Lp : VerifiableInference.Desc.K12.Door.Laid) (o : ℕ) (seat : ℕ × ℕ) (a : ℕ) : Bool :=
  match Lp.places[o]? with
  | some q => decide (q.2 = seat.2) &&
    match Lp.shapes[q.1]? with
    | some sh0 => decide (sh0.logN = a) &&
      match d? with
      | some d =>
        decide ((sh0.mainSymbols.extract 0 seat.2).foldl (· + ·) 0 = d.mainSkip seat.2) &&
          decide (sh0.mainWidth + (sh0.maskSymbols.extract 0 seat.2).foldl (· + ·) 0 =
            d.maskSkip seat.2)
      | none => true
    | none => false
  | none => false

/-- **THE TIE.** -/
theorem planClosedB_is {Xi : Type} (G : FileDescription Xi)
    (Lp : VerifiableInference.Desc.K12.Door.Laid) (o : ℕ) (seat : ℕ × ℕ) (a : ℕ) :
    planClosedB G Lp o seat a = planClosedO (G.oracleAt seat.1) Lp o seat a := rfl

/-- Where the first chain's cut is the written one: what is told of a tree below 83. -/
theorem oracleAt_of_cut {Xi : Type} (F : FileDescription Xi) (hc : cutOf F.first.blocksInOrder = cutFirstFull)
    {j : ℕ} (hj : j < 83) : F.oracleAt j = toldCut.flatten[j]? := by
  have hA : oraclesOf F.first.blocksInOrder = toldCut.flatten := by
    rw [oraclesOf_told, (told_at_written hc).2]
  have hL : toldCut.flatten.length = 83 := cut_tells.2.2
  unfold FileDescription.oracleAt
  rw [hA, List.getElem?_append_left (by rw [List.length_append, hL]; omega),
    List.getElem?_append_left (by rw [hL]; exact hj)]

/-- The closed test at one link; l': the link at which the members' numbers are read. -/
def closedLinkB (os : List VerifiableInference.Desc.Oracle) (l l' : ℕ) : Bool :=
  (List.finRange (loAt l).length).all fun i =>
    decide ((seatK10 (loAt l) P5T.psFull l i).1 < 83) &&
      (os[(seatK10 (loAt l) P5T.psFull l i).1]?).isSome &&
      planClosedO os[(seatK10 (loAt l) P5T.psFull l i).1]? LFull
        (noK10 seatsFullW (loAt l) P5T.psFull l' i) (seatK10 (loAt l) P5T.psFull l i)
        (aOf codesFull2 ((loAt l).get i).1)

/-- The same at link 0's five-list. -/
def closedFiveB (os : List VerifiableInference.Desc.Oracle) : Bool :=
  (List.finRange loFive.length).all fun i =>
    decide ((seatFive i).1 < 83) && (os[(seatFive i).1]?).isSome &&
      planClosedO os[(seatFive i).1]? LFull (noFive i) (seatFive i)
        (aOf codesFull2 (loFive.get i).1)

set_option maxRecDepth 1000000 in
/-- **BY THE KERNEL, AT ALL 25.** -/
theorem closed_written : (List.range 25).all (fun l => closedLinkB toldCut.flatten l l) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **BY THE KERNEL, AT THE FIVE.** -/
theorem closed_five : closedFiveB toldCut.flatten = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative line: each tree handed its neighbour's telling. -/
theorem closed_can_fail :
    (List.range 25).all (fun l => closedLinkB (toldCut.flatten.drop 1) l l) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative line: the members' numbers read at the next link. -/
theorem closed_can_fail_no :
    (List.range 25).any (fun l => closedLinkB toldCut.flatten l (l + 1)) = false := by
  decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **(8), under the head, at all 25.** -/
theorem planClosed_at_head (h : AtMg o Z D r Zp Np cF)
    {Ld : VerifiableInference.Desc.K12.Door.Laid}
    (hLd : laidAtCodes Zp.first.codes Zp.made.proof.1 = some Ld) {l : ℕ} (hl : l < 25)
    (i : Fin (loAt l).length) :
    planClosedB (F0T o Zp Np cF) Ld (noK10 (At.seats Zp) (loAt l) (At.pseats Zp) l i)
      (seatK10 (loAt l) (At.pseats Zp) l i) (aOf (At.cs Zp) ((loAt l).get i).1) = true := by
  obtain rfl : LFull = Ld := Option.some.inj ((ld_at_laid h.scope h.laid).symm.trans hLd)
  have e1 : At.pseats Zp = P5T.psFull := h.seats
  have e2 : At.seats Zp = seatsFullW := by
    unfold At.seats seatsFullW
    rw [e1]
  have hc : cutOf (F0T o Zp Np cF).first.blocksInOrder = cutFirstFull := (pins_of_laid h.scope h.laid).2
  have k := List.all_eq_true.1 (List.all_eq_true.1 closed_written l (List.mem_range.2 hl)) i
    (List.mem_finRange i)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at k
  rw [e1, e2, h.codes_full, planClosedB_is, oracleAt_of_cut _ hc k.1.1]
  exact k.2

/-- **(8), under the head, at link 0's five-list.** -/
theorem planClosed_five_at_head (h : AtMg o Z D r Zp Np cF)
    {Ld : VerifiableInference.Desc.K12.Door.Laid}
    (hLd : laidAtCodes Zp.first.codes Zp.made.proof.1 = some Ld) (i : Fin loFive.length) :
    planClosedB (F0T o Zp Np cF) Ld (noFive i) (seatFive i) (aOf (At.cs Zp) (loFive.get i).1) =
      true := by
  obtain rfl : LFull = Ld := Option.some.inj ((ld_at_laid h.scope h.laid).symm.trans hLd)
  have hc : cutOf (F0T o Zp Np cF).first.blocksInOrder = cutFirstFull := (pins_of_laid h.scope h.laid).2
  have k := List.all_eq_true.1 closed_five i (List.mem_finRange i)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at k
  rw [h.codes_full, planClosedB_is, oracleAt_of_cut _ hc k.1.1]
  exact k.2

end IM.K10

#print axioms IM.K10.planClosedB_is
#print axioms IM.K10.oracleAt_of_cut
#print axioms IM.K10.closed_written
#print axioms IM.K10.closed_five
#print axioms IM.K10.closed_can_fail
#print axioms IM.K10.closed_can_fail_no
#print axioms IM.K10.planClosed_at_head
#print axioms IM.K10.planClosed_five_at_head
