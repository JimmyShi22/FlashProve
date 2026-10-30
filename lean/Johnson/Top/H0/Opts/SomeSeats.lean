-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Opts/SomeSeats.lean: the named conditions callsSomeB and digSomeB
(Johnson/P5J/Rad3Seat3Tests.lean: two of k3SeatsB's six: each member of a link's list of lookups is
alike to some member of the table, in shape, radius and tenant): THEIR HALF ON SHAPES AND TENANTS,
AS A TEST WITH CODE ON THE PLAN's SEATS AND THE REQUEST's SHAPE ALONE.
  seatsSomeB   the test: at each member of a list of shapes: some seat of the plan with a sample has
               that shape and sits at the member's tenant
  seatsSome_law  what it gives: the premise (A) of some_split
               (Opts/SomeSplit.lean) and A₁ | A₂ of k3Some_of_rows (Opts/SomeAtName.lean)
  calls_shapes · dig_shapes  THE SHAPES OF THE LOOKUPS' TWO LISTS HANG ON NO RADIUS: they are those
               of the lists at the radius 0 (P6T.listCallsAt | listAt)
  sentOf · someAt  the two tests at a shape S and a list of seats ps
  some_is      AT P5J.At's CLOSED LETTERS THE TWO TESTS ARE someAt (At.shape Zp) (At.pseats Zp) l:
               NEITHER THE LAYOUT FILE NOR A RADIUS IS READ
LIMITS. Definitions and unfoldings. Whether the test accepts is SomeSeatsWritten.lean's. The radii
are the other half. No soundness is claimed.
-/
import Johnson.P5J.Rad3Seat3Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1Opts
open OnBytes OnBytes.Params
open VerifiableInference.Desc.First.Look (Sent sigList sigListCalls lastMoment)
open P5T (PSeat)

/-- **THE TEST ON SHAPES AND TENANTS.** ps: the plan's seats. shapes: a list's shapes. seat: its
members' tenants. At each member: some seat of the plan with a sample has the member's shape and
sits at the member's tenant. -/
def seatsSomeB (ps : List PSeat) (shapes : List OracleShape) (seat : ℕ → ℕ × ℕ) : Bool :=
  (List.range shapes.length).all fun i =>
    ps.any fun p => p.smpd && decide (shapes[i]? = some p.shape) && decide (p.seat = seat i)

/-- **Its law.** -/
theorem seatsSome_law {ps : List PSeat} {L : List (OracleShape × ℕ)} {seat : ℕ → ℕ × ℕ}
    (h : seatsSomeB ps (L.map (·.1)) seat = true) (i : Fin L.length) :
    ∃ p ∈ ps, p.smpd = true ∧ p.shape = (L.get i).1 ∧ p.seat = seat i.1 := by
  have h1 := List.all_eq_true.1 h i.1 (List.mem_range.2 (by rw [List.length_map]; exact i.2))
  obtain ⟨p, hp, h2⟩ := List.any_eq_true.1 h1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
  obtain ⟨⟨a, b⟩, c⟩ := h2
  refine ⟨p, hp, a, ?_, c⟩
  rw [List.getElem?_map, List.getElem?_eq_getElem i.2] at b
  exact (Option.some.inj b).symm

/-- The calls' list's shapes hang on no radius. -/
theorem calls_shapes (D : Sent) (rad : OracleShape → ℕ) (l : ℕ) :
    (sigListCalls D rad l).map (·.1) = (P6T.listCallsAt D l).map (·.1) := by
  unfold P6T.listCallsAt sigListCalls sigList
  simp only [List.map_append, List.map_map]
  rfl

/-- Nor do the digits' list's. -/
theorem dig_shapes (D : Sent) (rad : OracleShape → ℕ) (l : ℕ) :
    (sigList D rad l (lastMoment D l)).map (·.1) = (P6T.listAt D l).map (·.1) := by
  unfold P6T.listAt sigList
  simp only [List.map_map]
  rfl

/-- A value of the lookups' structure with the shape S and nothing else. -/
def sentOf (S : ReqShape) : Sent := ⟨{}, S, ⟨[]⟩, #[]⟩

/-- **The two tests' texts**, at a shape and a list of seats. -/
def someAt (S : ReqShape) (ps : List PSeat) (l : ℕ) : Bool :=
  seatsSomeB ps ((P6T.listCallsAt (sentOf S) l).map (·.1)) (P6T.seatCallsT ps (sentOf S) l) &&
    seatsSomeB ps ((P6T.listAt (sentOf S) l).map (·.1)) (P6T.seatT ps l)

/-- **At P5J.At's closed letters the two tests on shapes and tenants are someAt**: they read the
plan's shape and the plan's seats, and neither the layout file nor a radius. -/
theorem some_is (Zp : ProofFile.Pub) (lay : ByteArray) (l : ℕ) :
    (seatsSomeB (P5J.At.pseats Zp) ((P5J.At.callsListAt Zp lay l).map (·.1))
        (P5J.At.seat3At Zp l false) &&
      seatsSomeB (P5J.At.pseats Zp) ((P5J.At.digListAt Zp lay l).map (·.1))
        (P5J.At.seat3At Zp l true)) = someAt (P5J.At.shape Zp) (P5J.At.pseats Zp) l := by
  unfold P5J.At.callsListAt P5J.At.digListAt
  rw [calls_shapes, dig_shapes]
  rfl

end P1Opts

#print axioms P1Opts.seatsSome_law
#print axioms P1Opts.calls_shapes
#print axioms P1Opts.dig_shapes
#print axioms P1Opts.some_is
