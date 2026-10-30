-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/HB/LLHARD/MaskSeatWritten.lean: the closed facts on the seat of segment 24's mask row
that the condition "the state holds the mask row's seat" (MaskSeatAt,
Johnson/Desc/Kinds/Law/MaskRowsOne.lean) and the lemma that joins the two sentences for "weights"
ask of the table's numbers: at the written values by evaluation in Lean's kernel, and under the
structure of conditions `P5J.AtMg` (Johnson/P5J/AtMg.lean) at that structure's own numbers. Theorems
with their proofs.

Why. Two sides name the mask row's message in two ways. The merge's side: the seat at which the
maker's list of seats has, as segment 24's own, the first message of that segment's list with mask
rows (`Sound.maskPlace`, Johnson/Desc/Sound/MgAt/K11MembersAt.lean). The output head's side: the
witness's number of message 0 of segment 24 (`At.num Zp 24 0`). If the two did not meet, the
condition on the state could be met at no state. Here: they meet, at the seat (73, 2).

How. In the goals' scope, where the value is laid and two comparisons with written values accept,
the lists of seats, the core of the numbers and the request's shape are the written ones
(`seats_in_scope`, Johnson/P5T/PlanSeatsTie.lean; `first_written_in_scope` with
`request_shape_written`). At the written values each fact is one evaluation.

TO COMPILE IT: Johnson/Desc/Sound/MgAt/K11Members.lean and K11MembersAt.lean, which it imports, were
not in the library over which it was compiled: they were laid beside it, untouched, and compiled
first.

Main names. At the written values:
  `place_written`: `maskPlace psFull shapeFull 24 = some (73, 2)`; `no_written`: `maskNo shapeFull
    24 = some 0`.
  `num_written`: `arrOf seatsAllFull 73 2 = numOfPlan seatsAllFull 24 0`. `key_there`: that number
    is below the number of keys: so the equation is not the idle one (see the Limits).
  `sent_written`: (73, 2) ∈ N0Full.sent 24 0.
  `named_written`: `namedOnce (arrOf seatsAllFull) N0Full 24 (numOfPlan seatsAllFull 24 0) = true`.
  NEGATIVE TESTS: `num_rejects`: at the seat (73, 1) the number is another; `sent_rejects`: (74, 0)
    is no seat of the segment's first sending; `named_rejects`: the number of message 1 of segment
    23 does not name just one seat of segment 24's group.
  `rows_fit`, `cols_fit`: two premises of the joining lemma that have no parameter in them: the
    committed table's numbers of rows and of columns at the full size are at most the reference
    layout's.
Under the structure, at every o:
  `AtMg.seats_written`, `AtMg.shape_written`: the two lists of seats, the core of the numbers and
    the request's shape are the written ones.
  `AtMg.mask_place`, `AtMg.mask_num`, `AtMg.mask_sent`, `AtMg.mask_named`: the four facts at
    `P5T.planSeats Zp Zp.D.1` and `Zp.first.shape`, at `At.arr Zp`, `At.num Zp` and `At.N Zp cF`.

Limits. A member of `AtMg` is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library
AtFullSide/Top/): where there is none, the six under it speak of nothing.
THEY OPEN TWO OF THE STRUCTURE's OWN CONDITIONS: the comparison of what is made for these public
files with written values, `madePinnedAt` (out of the field asks of `LaidAt`, by `pins_of_laid`,
Johnson/Goal/Skeleton/PinsOfLaid.lean), and the test on the declared rounds on which "the value is
laid" rests: so they are facts on the written values; nothing is said on what the maker returns at
the shipped files. (All thirteen tests of the field asks have been seen to accept at the release's
three public files, at o := `OnBytes.secondHashFunction` alone, by an evaluation (Lean's evaluator; no theorem);
that evaluation is not called here.) (The list of these tests, `LPFD.lawsAsk`, has fourteen entries
in this library: of the fourteenth nothing is said here.)
Of the fields of `AtMg` two are spent: scope and laid (of it
pub, value, planOk, data and asks). AN IDLE CASE OF THE EQUATION `num_written`: at a seat outside
its list `arrOf` gives the number of keys, and so does `numOfPlan` at a key that no seat has: the
equation holds at every absent seat and absent key. It is not the case here: `key_there`.
`named_rejects` says "not just one": none, or two and more; which, is not said; no test here probes
two seats with one number. `sent_rejects`: that (74, 0) is a seat at all (by another print: of the
segment's second sending) is not shown here: an absent pair would be rejected too. That the book of
trees of a reached state has the message at (73, 2) is not said here. The full size alone. Nothing
on soundness.

-/
import Johnson.P5J.AtMg
import Johnson.P5J.LettersAt
import Johnson.Goal.Skeleton.PinsOfLaid
import Johnson.P5T.PlanSeatsTie
import Johnson.Desc.Laid.ProofFullLaw
import Johnson.Desc.Sound.ReadAt
import Johnson.Desc.Sound.MgAt.K11MembersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (maskPlace maskNo namedOnce)
open VerifiableInference.Desc.ReqLit (shapeFull)
open P5T (psFull seatsAllFull N0Full arrOf numOfPlan)
open OnBytes.Maker (WholeD)

/-! ## At the written values -/

set_option maxRecDepth 1000000 in
/-- The first message of segment 24's list with mask rows is number 0. -/
theorem no_written : maskNo shapeFull 24 = some 0 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The merge's side's seat of the mask row. -/
theorem place_written : maskPlace psFull shapeFull 24 = some (73, 2) := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **The two sides meet**: the witness's number at that seat is the number of message 0 of segment
24. -/
theorem num_written : arrOf seatsAllFull 73 2 = numOfPlan seatsAllFull 24 0 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- That number is a message's: it is below the number of keys, which both sides of the equation
give where the seat, or the key, is absent. -/
theorem key_there :
    numOfPlan seatsAllFull 24 0 < ((seatsAllFull.map P5T.keyOf).eraseDups).length := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- NEGATIVE TEST: at the seat beside it the number is another. -/
theorem num_rejects : arrOf seatsAllFull 73 1 ≠ numOfPlan seatsAllFull 24 0 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The seat is one of the segment's first sending's. -/
theorem sent_written : ((73, 2) : ℕ × ℕ) ∈ N0Full.sent 24 0 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- NEGATIVE TEST: (74, 0) is no seat of the first sending. -/
theorem sent_rejects : ((74, 0) : ℕ × ℕ) ∉ N0Full.sent 24 0 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Segment 24's group has just one seat with that number. -/
theorem named_written :
    namedOnce (arrOf seatsAllFull) N0Full 24 (numOfPlan seatsAllFull 24 0) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- NEGATIVE TEST: the number of a message of another segment does not name just one seat of the
group. -/
theorem named_rejects :
    namedOnce (arrOf seatsAllFull) N0Full 24 (numOfPlan seatsAllFull 23 1) = false := by
  decide +kernel

/-! ## The committed table's two sizes -/

/-- The committed table has at most the reference layout's number of rows. (The library has the
equation: `full_rows`, Johnson/Flat/ClaimsSizes.lean.) -/
theorem rows_fit : OnBytes.Flat.numsFull.rows ≤ Inst.Model.Layout.hRef := by decide +kernel

set_option maxRecDepth 1000000 in
/-- And at most the reference layout's number of columns. -/
theorem cols_fit : colsAt OnBytes.Flat.numsFull ≤ 2 ^ Inst.Model.Layout.kRef := by decide +kernel

/-! ## Under the structure -/

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- The lists of seats and the core of the numbers are the written ones. -/
theorem AtMg.seats_written (h : AtMg o Z D r Zp Np cF) :
    P5T.planSeats Zp Zp.D.1 = psFull ∧ P5T.planSeatsAll Zp Zp.D = seatsAllFull ∧
      P5T.numbersOf (P5T.planSeats Zp Zp.D.1) = N0Full :=
  P5T.seats_in_scope h.scope h.laid.pub (pins_of_laid h.scope h.laid).1
    (LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks)

/-- The request's shape is the written one. -/
theorem AtMg.shape_written (h : AtMg o Z D r Zp Np cF) : Zp.first.shape = shapeFull :=
  (VerifiableInference.PlanWritten.Joined.first_written_in_scope h.scope h.laid.pub
    (pins_of_laid h.scope h.laid).1).2.2.1.trans
    VerifiableInference.PlanWritten.request_shape_written

/-- The merge's side's seat of the mask row is (73, 2). -/
theorem AtMg.mask_place (h : AtMg o Z D r Zp Np cF) :
    maskPlace (P5T.planSeats Zp Zp.D.1) Zp.first.shape 24 = some (73, 2) := by
  rw [h.seats_written.1, h.shape_written]
  exact place_written

/-- **The two sides meet.** -/
theorem AtMg.mask_num (h : AtMg o Z D r Zp Np cF) : At.arr Zp 73 2 = At.num Zp 24 0 := by
  unfold At.arr At.num At.pseatsAll
  rw [h.seats_written.2.1]
  exact num_written

/-- The seat is one of the segment's first sending's. -/
theorem AtMg.mask_sent (h : AtMg o Z D r Zp Np cF) :
    ((73, 2) : ℕ × ℕ) ∈ (At.N Zp cF).sent 24 0 := by
  have e : (At.N Zp cF).sent = N0Full.sent := congrArg (·.sent) h.seats_written.2.2
  rw [e]
  exact sent_written

/-- Segment 24's group has just one seat with that number. -/
theorem AtMg.mask_named (h : AtMg o Z D r Zp Np cF) :
    namedOnce (At.arr Zp) (At.N Zp cF) 24 (At.num Zp 24 0) = true := by
  have e : (At.N Zp cF).sent = N0Full.sent := congrArg (·.sent) h.seats_written.2.2
  have g : (At.N Zp cF).group 24 = N0Full.group 24 := by
    unfold VerifiableInference.Desc.First.Numbers.group
    rw [e]
  unfold namedOnce
  rw [g]
  unfold At.arr At.num At.pseatsAll
  rw [h.seats_written.2.1]
  exact named_written

end P5J

#print axioms P5J.no_written
#print axioms P5J.place_written
#print axioms P5J.num_written
#print axioms P5J.key_there
#print axioms P5J.num_rejects
#print axioms P5J.sent_written
#print axioms P5J.sent_rejects
#print axioms P5J.named_written
#print axioms P5J.named_rejects
#print axioms P5J.rows_fit
#print axioms P5J.cols_fit
#print axioms P5J.AtMg.seats_written
#print axioms P5J.AtMg.shape_written
#print axioms P5J.AtMg.mask_place
#print axioms P5J.AtMg.mask_num
#print axioms P5J.AtMg.mask_sent
#print axioms P5J.AtMg.mask_named
