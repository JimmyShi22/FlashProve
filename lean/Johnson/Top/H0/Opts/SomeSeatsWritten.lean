-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Opts/SomeSeatsWritten.lean: the named conditions callsSomeB and digSomeB
(Johnson/P5J/Rad3Seat3Tests.lean: two of k3SeatsB's six): THEIR HALF ON SHAPES AND TENANTS, AT THE
WRITTEN VALUES, BY LEAN's KERNEL, AND AT P5J.At's CLOSED LETTERS WHERE THE PLAN's SHAPE AND SEATS
ARE THE WRITTEN ONES.
  some_written  SomeSeats.lean's someAt accepts at all 25 segments at the written
                values proofSizedFull.request (the request's shape) and psFull (the plan's seats of
                the first chain: Johnson/P5T/PlanSeatsFull.lean): by decide +kernel
  some_rejects_seat · some_rejects_shape  two negative tests: one tenant bent in the plan's seats
                alone; one main row more at the list's first member: the test rejects
  seats_at_written  so both tests accept at P5J.At's letters, at every layout file
  a1_at_written · a2_at_written  THE PREMISES A₁ | A₂ OF k3Some_of_rows
                (Opts/SomeAtName.lean), TO THE LETTER
THE TWO PREMISES. hS : At.shape Zp = proofSizedFull.request · hp : At.pseats Zp = psFull: JUST WHAT
k3Four_at_name (Johnson/HB/LLHARD/K3SeatsFour.lean :130-135) draws, in scope,
out of LaidAt and the pin hy (madePinnedAt …), by first_written_in_scope and seats_in_scope.
THESE TWO ARE NOT CALLED HERE:
hS and hp stay premises.
LIMITS. The full size alone. The radii are not spoken of: they are the other half (one shape, one
radius in the first chain's rows; the rows' shapes are the plan's). No soundness is claimed.

-/
import Johnson.Top.H0.Opts.SomeSeats
import Johnson.P5T.PlanSeatsFull
import Johnson.Desc.Ok.PlanWritten.SizedLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1Opts
open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten (proofSizedFull)
open P5T (PSeat psFull)
open P5J (At.pseats At.shape At.links At.callsListAt At.digListAt At.seat3At)

set_option maxRecDepth 1000000 in
/-- **They accept at all 25 segments, at the written values.** -/
theorem some_written :
    ((List.range 25).all fun l => someAt proofSizedFull.request psFull l) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: the plan's seats with one tenant bent, against the unbent tenants. -/
theorem some_rejects_seat :
    seatsSomeB (P6T.bumped psFull 0) ((P6T.listAt (sentOf proofSizedFull.request) 0).map (·.1))
      (P6T.seatT psFull 0) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A second**: the list with one main row more at its first member. -/
theorem some_rejects_shape :
    seatsSomeB psFull ((P6T.widened (sentOf proofSizedFull.request) 0).map (·.1))
      (P6T.seatT psFull 0) = false := by decide +kernel

section
variable {Zp : ProofFile.Pub}

/-- **THE TWO TESTS ON SHAPES AND TENANTS, AT P5J.At's CLOSED LETTERS, WHERE THE PLAN's SHAPE AND
SEATS ARE THE WRITTEN ONES.** -/
theorem seats_at_written (hS : At.shape Zp = proofSizedFull.request) (hp : At.pseats Zp = psFull)
    (lay : ByteArray) {l : ℕ} (hl : l < At.links.length) :
    seatsSomeB (At.pseats Zp) ((At.callsListAt Zp lay l).map (·.1)) (At.seat3At Zp l false) = true ∧
      seatsSomeB (At.pseats Zp) ((At.digListAt Zp lay l).map (·.1)) (At.seat3At Zp l true) =
        true := by
  have w : someAt (At.shape Zp) (At.pseats Zp) l = true := by
    rw [hS, hp]
    exact List.all_eq_true.1 some_written l (List.mem_range.2 hl)
  exact Eq.mp (Bool.and_eq_true _ _) ((some_is Zp lay l).trans w)

/-- **(A) AT THE CALLS' LIST**, in the letters of SomeAtName.lean's k3Some_of_rows (A₁). -/
theorem a1_at_written (hS : At.shape Zp = proofSizedFull.request) (hp : At.pseats Zp = psFull)
    (lay : ByteArray) : ∀ l, l < At.links.length → ∀ i : Fin (At.callsListAt Zp lay l).length,
      ∃ p ∈ At.pseats Zp, p.smpd = true ∧ p.shape = ((At.callsListAt Zp lay l).get i).1 ∧
        p.seat = At.seat3At Zp l false i.1 :=
  fun _ hl i => seatsSome_law (seats_at_written hS hp lay hl).1 i

/-- **(A) AT THE DIGITS' LIST** (A₂). -/
theorem a2_at_written (hS : At.shape Zp = proofSizedFull.request) (hp : At.pseats Zp = psFull)
    (lay : ByteArray) : ∀ l, l < At.links.length → ∀ i : Fin (At.digListAt Zp lay l).length,
      ∃ p ∈ At.pseats Zp, p.smpd = true ∧ p.shape = ((At.digListAt Zp lay l).get i).1 ∧
        p.seat = At.seat3At Zp l true i.1 :=
  fun _ hl i => seatsSome_law (seats_at_written hS hp lay hl).2 i

end

end P1Opts

#print axioms P1Opts.some_written
#print axioms P1Opts.some_rejects_seat
#print axioms P1Opts.some_rejects_shape
#print axioms P1Opts.seats_at_written
#print axioms P1Opts.a1_at_written
#print axioms P1Opts.a2_at_written
