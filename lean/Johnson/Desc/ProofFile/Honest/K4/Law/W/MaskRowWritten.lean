-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/MaskRowWritten.lean: CONDITIONAL. Two abbreviations,
statements with their proofs.

What is here. Law/W/MaskSixHead.lean has, from the public side alone, a member u of the witness's
list at the mask row of the segment of the feed-forward layers' own rounds (sub-protocol K4); u
stands there under ∃. HERE WHAT A DEFINITION NEEDS OF u IS WRITTEN AS TERMS THAT NAME NO u: whoever
must write a term (a script's message number, a bound on the entries that are read) cannot take u
out of an ∃. `maskPosOf D i`: an index into the list of the oracle messages that stand sent at link
i (the kept ones first, then link i's own of moment 0, while the search runs over all of link i's:
outside `MaskRowPub` the index can point behind the list): it points at link i's first message that
has mask rows: a search's value. Under `MaskRowPub`: u's seat is the plan's seat at that place
(`maskRow_seat`); u's number in the witness, `numOf h.𝔇.arr u`, is `h.𝔇.arr` at that seat
(`maskRow_num`); u's shape is the shape that the list holds at that place (`maskRow_shape`); so the
mask code's length at u's shape is the length at that shape (`maskRow_ell`); and that length is at
least 1 where the lookup's place has an entry of the mask row (`maskRow_ell_pos`). THE TERMS STILL
NAME THE LOOKUP's PLACE xl, through its field link alone, which is the segment's number m
(`layAt_laid`, Law/W/LayAtHead.lean): Law/W/MaskRowAtSeg.lean has them at m, and without h.
How. The field seat of `MaskRowPub`, and unfolding.

Not shown here. THAT `MaskRowPub` HOLDS: `maskRowPub_head` (Law/W/MaskSixHead.lean) has it under the
library's hypothesis on the public files, `LaidK4` and hx; every limit of that file's head holds
here. WHERE THE LINK HAS NO MESSAGE WITH MASK ROWS `maskPosOf` ANSWERS AS IF THE FIRST HAD: the
search's default is 0; under `MaskRowPub` there is one. What the terms are worth as numbers. THE
TERMS NAME h, through five fields of `h.𝔇` (Johnson/P5J/MgAtAll.lean) that take no field of the
proof: Law/W/MaskRowAtSeg.lean has them in the public part, the layout file and m alone. h1 (1 ≤
xl.ns, that is 1 ≤ (parOf x).hp.ns), the hypothesis of `maskRow_ell_pos`, is not shown here;
Law/W/MaskEllHead.lean has the length as a number without it. THAT THE NUMBERS OF TWO SEGMENTS
DIFFER: Law/W/MaskNumsApart.lean has it, under h, of the twelve segments of the feed-forward layers'
own rounds. That h can hold: the side library AtFullSide proves, with no hypothesis, that h has a
member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). THE FULL SIZE ALONE, and the format's second hash function alone, wherever
h is asked. A program's walk from import to import, which reads import lines alone and stops
unopened at Johnson/Goal/, ThirdParty/, Johnson/D/, Johnson/Bridge/ and Cb/Bridge*, stopped at 70
modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins Cb.Bridge: floors. A
LAW, NOT A PART: no file that defines a part of the proof file's description may import this one.
Nothing on soundness, on completeness or on any other property. No property is claimed.

  `maskMsgOf`, `maskPosOf`   the search's value; the place in the list: abbreviations of
      `Lot.k4MaskMsg`, `Lot.k4MaskPos` (Lot/MaskNum.lean), where the texts lie
  `maskPos_is`   under `MaskRowPub` the place is the one that its field seat names
  `maskRow_seat`, `maskRow_num`   **u's seat and number, written**
  `maskRow_shape`, `maskRow_ell`, `maskRow_ell_pos`   **u's shape and the code's length, written**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskSixHead
import Johnson.Desc.ProofFile.Honest.K4.Lot.MaskNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open Johnson.Pack (pMask)
open OnBytes.Road.K4.Rec (RecPlan)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (Sent messagesAt keptAt sigListCalls)
open VerifiableInference.Desc.Sound (Mem seatOf numOf)
open P5J (AtMgA TS)

/-- The number, among link i's oracle messages, of the first with mask rows; 0 where there is
none. An abbreviation: the text is `Lot.k4MaskMsg`'s (Lot/MaskNum.lean). -/
abbrev maskMsgOf (D : Sent) (i : ℕ) : ℕ := Lot.k4MaskMsg D i

/-- Its place in the list of the oracle messages that stand sent at link i: behind the kept ones.
An abbreviation: the text is `Lot.k4MaskPos`'s (Lot/MaskNum.lean). -/
abbrev maskPosOf (D : Sent) (i : ℕ) : ℕ := Lot.k4MaskPos D i

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  {h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh} {R : RecPlan} {n m : ℕ}
  {xl : VerifiableInference.Desc.First.Look.Place} {o : ℕ} {u : Mem}

/-- CONDITIONAL on P. The place is within the list; u's seat and shape are the plan's at it. -/
theorem maskPos_is (P : MaskRowPub h R n m xl o u) :
    ∃ hm : maskPosOf h.𝔇.sent xl.link < (sigListCalls h.𝔇.sent h.𝔇.l3.rad xl.link).length,
      seatOf u = h.𝔇.l3.seat xl.link false (maskPosOf h.𝔇.sent xl.link) ∧
      (u.1.l.get u.2).1 = ((sigListCalls h.𝔇.sent h.𝔇.l3.rad xl.link).get ⟨_, hm⟩).1 := by
  obtain ⟨mI, hm, hf, hs, hsh⟩ := P.seat
  have e : maskPosOf h.𝔇.sent xl.link = (keptAt h.𝔇.sent xl.link).length + mI :=
    congrArg (fun t : Option ℕ => (keptAt h.𝔇.sent xl.link).length + t.getD 0) hf
  rw [e]
  exact ⟨hm, hs, hsh⟩

/-- CONDITIONAL on P. **u's SEAT, WRITTEN.** -/
theorem maskRow_seat (P : MaskRowPub h R n m xl o u) :
    seatOf u = h.𝔇.l3.seat xl.link false (maskPosOf h.𝔇.sent xl.link) :=
  (maskPos_is P).2.1

/-- CONDITIONAL on P. **u's NUMBER IN THE WITNESS, WRITTEN.** -/
theorem maskRow_num (P : MaskRowPub h R n m xl o u) :
    numOf h.𝔇.arr u =
      h.𝔇.arr (h.𝔇.l3.seat xl.link false (maskPosOf h.𝔇.sent xl.link)).1
        (h.𝔇.l3.seat xl.link false (maskPosOf h.𝔇.sent xl.link)).2 := by
  have e := maskRow_seat P
  show h.𝔇.arr (seatOf u).1 (seatOf u).2 = _
  rw [e]

/-- CONDITIONAL on P. **u's SHAPE, WRITTEN**: what the list holds at the place. -/
theorem maskRow_shape (P : MaskRowPub h R n m xl o u) :
    ((sigListCalls h.𝔇.sent h.𝔇.l3.rad xl.link)[maskPosOf h.𝔇.sent xl.link]?).map (·.1) =
      some (u.1.l.get u.2).1 := by
  obtain ⟨hm, -, hsh⟩ := maskPos_is P
  rw [List.getElem?_eq_getElem hm]
  exact congrArg some hsh.symm

/-- CONDITIONAL on P. **THE MASK CODE's LENGTH AT u's SHAPE, WRITTEN.** -/
theorem maskRow_ell (P : MaskRowPub h R n m xl o u) :
    ((sigListCalls h.𝔇.sent h.𝔇.l3.rad xl.link)[maskPosOf h.𝔇.sent xl.link]?).map
        (fun z => (pMask h.𝔇.cs z.1).ell) = some (pMask h.𝔇.cs (u.1.l.get u.2).1).ell := by
  obtain ⟨hm, -, hsh⟩ := maskPos_is P
  rw [List.getElem?_eq_getElem hm]
  exact congrArg (fun s => some (pMask h.𝔇.cs s).ell) hsh.symm

/-- CONDITIONAL on P and h1. The length is at least 1 where the place has an entry of the mask
row. -/
theorem maskRow_ell_pos (P : MaskRowPub h R n m xl o u) (h1 : 1 ≤ xl.ns) :
    1 ≤ (pMask h.𝔇.cs (u.1.l.get u.2).1).ell :=
  Nat.le_trans h1 P.room

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.maskPos_is
#print axioms ProofFile.Honest.K4.W.maskRow_seat
#print axioms ProofFile.Honest.K4.W.maskRow_num
#print axioms ProofFile.Honest.K4.W.maskRow_shape
#print axioms ProofFile.Honest.K4.W.maskRow_ell
#print axioms ProofFile.Honest.K4.W.maskRow_ell_pos
