-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Loose/H2K12/ClearAtHead.lean:
THE LAW OF THE PROXIMITY
TEST (the kind K12) ON THE PROOF FILE's FIRST CHAIN: ONE FIELD OF K12's FILES' SHORTER LIST OF DEBTS
(K12Rest₆.clear, K12LeftOfRest.lean; it is K12Left's field clear, handed through): what the row
at sub-protocol number 354 lays is none of the three components of the witness that the riders read
(Rid354.clearB, H2K12/Rides354.lean), at the one head (P5J.AtMgA). Statements and proofs.
BY TWO ROADS:
  clearB_told     the test reads nothing of what withRows (Johnson/Desc/First/RowsAtPlan.lean) and
                  withTold (Johnson/Desc/First/BookNumbers.lean) lay over the numbers.
  clear_full354   the test at the written seats and the core of the numbers (seatsAllFull, N0Full,
                  Johnson/P5T/PlanSeatsFull.lean), at the one number: decided by the kernel.
                  clear_full354_no: it can fail: with the index masks' seat laid at the seat of the
                  test's own member it does. (That a test can fail does not show that the premises
                  below can be met.)
  clear_of_pins   the test at the computed terms, where the two lists of seats off the list of
                  rounds are the written ones.
  clear_atMg      THE FIELD TO THE LETTER, PAID UNDER THE PINS' EQUATIONS (WrittenAll354,
                  H2K12/ClosedOfPins354.lean).
  clear_at_head   the field from "at no sub-protocol does an item that rides read a component that
                  the row lays" (RidersClearQ, Johnson/Desc/Sound/BordersSides.lean) at the head's
                  letters: that statement at the head is other files' to show; until it lies on a
                  list THIS ROAD RENAMES THE DEBT AND PAYS NOTHING.
ITS KIN: clear_full (Johnson/Desc/First/Link/Law/ClearAtCore.lean)
decides the table's wider test laysClear over all 358 places; clear_full354 asks of one place, and
reads the numbering of the witness's messages at two seats.
Limits. (1) WrittenAll354 is a premise of clear_atMg: its payer from a test on the public part is
typed in that file. (2) RidersClearQ is a premise of clear_at_head. (3) The full size alone. No
soundness statement. Nothing on hiding.

-/
import Johnson.P5J.MgAtAll
import Johnson.Loose.H2K12.ClosedOfPins354
import Johnson.Loose.H2K12.ClosedMembers354

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (ModelPart Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)

/-- The test reads nothing of what is laid over the core of the numbers. -/
theorem clearB_told (arr : ℕ → ℕ → ℕ) (N : Numbers) (sh : OnBytes.Params.ReqShape) (g : ℕ → ℕ)
    (n : ℕ) (ps' : List Place) (told : List (List VerifiableInference.Desc.Oracle))
    (links : List ModelPart) (ps : List Place) (k : ℕ) :
    Rid354.clearB arr ((N.withRows sh g n).withTold ps' told) links ps k =
      Rid354.clearB arr N links ps k := rfl

set_option maxRecDepth 1000000 in
/-- By the kernel: the test at the written seats and the core of the numbers, at number 354. -/
theorem clear_full354 : Rid354.clearB (P5T.arrOf P5T.seatsAllFull) P5T.N0Full linksFull
    (flatPlacesOf linksFull true) 354 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can fail: with the index masks' seat laid at the seat of the test's own member. -/
theorem clear_full354_no : Rid354.clearB (P5T.arrOf P5T.seatsAllFull)
    { P5T.N0Full with index := (76, 0) } linksFull (flatPlacesOf linksFull true) 354 = false := by
  decide +kernel

/-- The test at the computed terms. -/
theorem clear_of_pins {Zp : ProofFile.Pub} (hP : P5T.planSeats Zp Zp.D.1 = P5T.psFull)
    (hA : P5T.planSeatsAll Zp Zp.D = P5T.seatsAllFull) (sh : OnBytes.Params.ReqShape) (g : ℕ → ℕ)
    (n : ℕ) (ps' : List Place) (told : List (List VerifiableInference.Desc.Oracle)) :
    Rid354.clearB (P5T.arrOf (P5T.planSeatsAll Zp Zp.D))
      (((P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).withRows sh g n).withTold ps' told) linksFull
      (flatPlacesOf linksFull true) 354 = true := by
  rw [clearB_told, hP, hA]
  exact clear_full354

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE FIELD TO THE LETTER, PAID UNDER THE PINS' EQUATIONS.** -/
theorem clear_atMg (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (W : WrittenAll354 Zp) :
    Rid354.clearB h.𝔇.arr (P5J.At.N Zp cF) P5J.fullLinks P5J.At.ps 354 = true :=
  clear_of_pins (pseats_written W.toWritten354) (pseatsAll_written W) _ _ _ _ _

/-- **The field from the rule's premise at the head's letters**: a debt renamed. -/
theorem clear_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hc : VerifiableInference.Desc.Sound.RidersClearQ (P5J.At.arr Zp) (P5J.At.N Zp cF)
      P5J.fullLinks P5J.At.ps) :
    Rid354.clearB h.𝔇.arr (P5J.At.N Zp cF) P5J.fullLinks P5J.At.ps 354 = true :=
  clear_354_of_riders _ _ hc

end

end H2K12

#print axioms H2K12.clearB_told
#print axioms H2K12.clear_full354
#print axioms H2K12.clear_full354_no
#print axioms H2K12.clear_of_pins
#print axioms H2K12.clear_atMg
#print axioms H2K12.clear_at_head
