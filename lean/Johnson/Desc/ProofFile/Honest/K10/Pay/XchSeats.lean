-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchSeats.lean: the closing of a segment (K10): closed tests, by Lean's kernel, at the written
plan: the seat and the shape that the plan gives the group's member at the place j of the group's list are the seat and the
shape of the code switch's message number j. For the fields stand of `TieBySwitch` (Pay/XchTieBySwitch.lean): a law on a
reached state (Pay/SeatsAtStand.lean) speaks in the plan's terms (`seatK10`, `loAt`, `membersOf`); the laws on the first chain's
script speak of the seat that `switchSeatIn` (Honest/K2/SwitchNums.lean) finds.

  `seatTest`, **`seat_written`**   at segments 1 to 24, at each j below the sending's messages less one: the list of members has a j-th,
                    i; the list of all seats has a seat q of "link l, moment 0", place j; `seatK10` at i is (q.j, q.t + d), d = 0;
                    the written list's shape at i is the shape of the switch's message number j. And the group has just two
                    members more than these
  `seat_bent`         THE TEST CAN FAIL: at d = 1 it rejects at every segment
  **`seat_at_switch`**         what the test says at one segment and one j, as equations
  `count_at_switch`          the count of the group's members at one segment

Limits. Written values alone, at the full size. That the head's lists of seats are the written ones is the library's
(`AtMg.seats_written`, Johnson/HB/LLHARD/MaskSeatWritten.lean).
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchPublic
import Johnson.Desc.ProofFile.Honest.K2.SwitchNums
import Johnson.Desc.First.Close.Law.SeatsOfLink
import Johnson.LPFE1R.RowPubAt
import Johnson.P5T.PlanSeatsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc.First.Close (seatK10)
open VerifiableInference.Desc.LinkJoin (loAt)
open ProofFile.Honest.K2 (SwitchPlace switchSent switchSeatIn)
open ProofFile.Honest.K2.Law (placesW)

/-- The test at segment l. d: a number added to the tenant that is asked for: 0 in the test. -/
def seatTest (d l : Nat) : Bool :=
  match placesW.find? (·.link == l) with
  | some p =>
    ((List.range ((switchSent p.sizes p.others).size - 1)).all fun j =>
      match (VerifiableInference.Desc.First.Close.membersOf (loAt l))[j]?, switchSeatIn P5T.seatsAllFull l j with
      | some i, some q =>
        decide (seatK10 (loAt l) P5T.psFull l i = (q.j, q.t + d)) &&
          decide (((loAt l).get i).1 = ((switchSent p.sizes p.others).getD j default).shape)
      | _, _ => false) &&
    decide ((VerifiableInference.Desc.First.Close.membersOf (loAt l)).length =
      (switchSent p.sizes p.others).size - 1 + 1 + 1)
  | none => false

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- **At segments 1 to 24 the plan's seats and shapes of the group's first members are the switch's messages'.** -/
theorem seat_written : ((List.range 24).all fun i => seatTest 0 (i + 1)) = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- The test can fail. -/
theorem seat_bent : ((List.range 24).any fun i => seatTest 1 (i + 1)) = false := by decide +kernel

/-- **What the test says at one segment and one place in the group's list.** -/
theorem seat_at_switch {l : Nat} (h1 : 1 ≤ l) (h2 : l < 25) {p : SwitchPlace} (hp : placesW.find? (·.link == l) = some p)
    {j : Nat} (hj : j + 1 < (switchSent p.sizes p.others).size) :
    ∃ i q, (VerifiableInference.Desc.First.Close.membersOf (loAt l))[j]? = some i ∧
      switchSeatIn P5T.seatsAllFull l j = some q ∧ seatK10 (loAt l) P5T.psFull l i = (q.j, q.t) ∧
      ((loAt l).get i).1 = ((switchSent p.sizes p.others).getD j default).shape := by
  have h := List.all_eq_true.1 seat_written (l - 1) (List.mem_range.2 (by omega))
  have e : l - 1 + 1 = l := by omega
  rw [e] at h
  unfold seatTest at h
  rw [hp] at h
  have h' := List.all_eq_true.1 (Eq.mp (Bool.and_eq_true _ _) h).1 j (List.mem_range.2 (by omega))
  cases hi : (VerifiableInference.Desc.First.Close.membersOf (loAt l))[j]? with
  | none =>
    rw [hi] at h'
    cases h'
  | some i =>
    cases hq : switchSeatIn P5T.seatsAllFull l j with
    | none =>
      rw [hi, hq] at h'
      cases h'
    | some q =>
      rw [hi, hq] at h'
      obtain ⟨a1, a2⟩ := Eq.mp (Bool.and_eq_true _ _) h'
      exact ⟨i, q, rfl, rfl, of_decide_eq_true a1, of_decide_eq_true a2⟩

/-- The count of the group's members at one segment. -/
theorem count_at_switch {l : Nat} (h1 : 1 ≤ l) (h2 : l < 25) {p : SwitchPlace} (hp : placesW.find? (·.link == l) = some p) :
    (VerifiableInference.Desc.First.Close.membersOf (loAt l)).length = (switchSent p.sizes p.others).size - 1 + 1 + 1 := by
  have h := List.all_eq_true.1 seat_written (l - 1) (List.mem_range.2 (by omega))
  have e : l - 1 + 1 = l := by omega
  rw [e] at h
  unfold seatTest at h
  rw [hp] at h
  exact of_decide_eq_true (Eq.mp (Bool.and_eq_true _ _) h).2

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.seat_written
#print axioms ProofFile.Honest.K10.seat_bent
#print axioms ProofFile.Honest.K10.seat_at_switch
#print axioms ProofFile.Honest.K10.count_at_switch
