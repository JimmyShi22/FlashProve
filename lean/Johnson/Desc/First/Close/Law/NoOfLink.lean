-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Close/Law/NoOfLink.lean (kind K10): A TERM, OFF THE PLAN, FOR THE NUMBER OF A
MEMBER OF A LINK's WRITTEN LIST AMONG THE STATEMENT's ORACLE MESSAGES; AND "THE BOOK PLACES THAT
MESSAGE AT THE PLAN's SEAT OF THE MEMBER" AT A STATE, FROM PUBLIC TESTS. Definitions with code, and
theorems: joins of lemmas.
Why. ViewText.lean's `wordsAre_of_msgs` takes hs: seatAt (no a) = some (seat a.1). The slots' names
(`namesOf`, NamesOfShapes.lean) stand in front of all statements: so no must be a term off the plan.
Another file's reader of samples numbers a member by the place of its seat in the plan's list
(`numAt`, Johnson/Desc/Sound/SmpNamed.lean): to agree with the samples that `faK10` lays, no must be
that.
  `noK10 seats lo ps l`: the place, in the plan's list of seats, of the i-th member's seat
    (`seatK10`, SeatsOfLink.lean). `noK10_is`: it is `numAt` at that member.
  `seat_at_book`: **where the promise's test on the book (`bookAt`) and the fold's tests
    "K12.seatsCarried", "K12.bookInOrder" (at 0) say yes, and the plan's first places name trees of
    the book: the first chain's reader places message o at the plan's o-th place**, o below the
    number of messages sent. By `seatFirst_atPlan` (Johnson/Desc/Sound/WordsAtPlan.lean),
    `numbers_of_book0`, `place_in_book` (Johnson/Desc/K12/Door/DoorGives.lean) and `book_place`
    (Johnson/Desc/First/Look/K3MaskOkTools.lean).
  `bookedAllB Ld n seats lo ps l`: ON PUBLIC DATA: each member's number lies below n, and the plan's
    list of places has the member's seat at it. `hs_k10`: **hs at `noK10` and `seatK10`, at the
    first chain's reader's own `seatBy noFirst s.book`.**
  `bookedAllB_yes`, `bookedAllB_late`, `bookedAllB_place`: THE TEST CAN SAY NO: by Lean's kernel at
    small written lists.
Limits. IMPLICATIONS ON ONE STATE. `bookedAllB` is evaluated at no plan here. That the statement's
group's members are these numbers, in order (`ShapesAre`, LayoutOfShapes.lean), is not said. Nothing
on soundness.

-/
import Johnson.Desc.First.Close.Law.SeatsOfLink
import Johnson.Desc.Sound.WordsAtDoor
import Johnson.Desc.Sound.SmpNamed
import Johnson.Desc.First.Look.K3MaskOkTools

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close
open OnBytes
open VerifiableInference.OnPublicFiles (book_place bookAt_sizes)
open VerifiableInference.Desc.First (S Numbers bookAt)
open VerifiableInference.Desc.Sound (seatBy noFirst seatFirst_atPlan numAt)
open VerifiableInference.Desc.K12.Door (Laid atFirstSeats atFirstBook placesBelowB numbers_of_book0
  place_in_book)

/-- **THE TERM FOR no**: the place of the member's seat in the plan's list of seats. -/
def noK10 (seats : List (ℕ × ℕ)) (lo : List (OracleShape × ℕ)) (ps : List P5T.PSeat) (l : ℕ) :
    Fin lo.length → ℕ := fun i => seats.idxOf (seatK10 lo ps l i)

/-- It is the number by which the reader of samples reads the member. -/
theorem noK10_is (seats : List (ℕ × ℕ)) (lo : List (OracleShape × ℕ)) (ps : List P5T.PSeat)
    (l : ℕ) (i : Fin lo.length) :
    noK10 seats lo ps l i = numAt seats ⟨⟨lo, seatK10 lo ps l⟩, i⟩ := rfl

variable {N : Numbers} {p : Option Desc.Place} {s : S} {Ld : Laid}

/-- **THE FIRST CHAIN's READER PLACES MESSAGE o AT THE PLAN's o-TH PLACE.** -/
theorem seat_at_book (hbook : bookAt N p s = true) (hseats : atFirstSeats Ld s = true)
    (hord : atFirstBook 0 s = true)
    (hb : placesBelowB Ld s.book.place.size s.book.trees.size = true) (o : ℕ) (q : ℕ × ℕ)
    (hlt : o < N.msgsAt p) (hpl : Ld.places[o]? = some q) :
    seatBy noFirst s.book o = some q := by
  obtain ⟨b1, b2⟩ := bookAt_sizes hbook
  obtain ⟨q', h1, h2⟩ := seatFirst_atPlan s.st s.book (numbers_of_book0 hord)
    (place_in_book hseats b1 hb) o (by rw [b2]; exact hlt)
  have h3 := book_place hbook hseats hlt hpl
  rw [h2, Option.some.inj (h1.symm.trans h3)]

/-- ON PUBLIC DATA: each member's number lies below n, and the plan's list of places has the
member's seat at it. -/
def bookedAllB (Ld : Laid) (n : ℕ) (seats : List (ℕ × ℕ)) (lo : List (OracleShape × ℕ))
    (ps : List P5T.PSeat) (l : ℕ) : Bool :=
  (List.range lo.length).all fun i =>
    decide (seats.idxOf ((seatsOfLink ps l).getD i (0, 0)) < n) &&
      Ld.places[seats.idxOf ((seatsOfLink ps l).getD i (0, 0))]? ==
        some ((seatsOfLink ps l).getD i (0, 0))

/-- **hs AT THE TWO TERMS.** -/
theorem hs_k10 (hbook : bookAt N p s = true) (hseats : atFirstSeats Ld s = true)
    (hord : atFirstBook 0 s = true)
    (hb : placesBelowB Ld s.book.place.size s.book.trees.size = true) (seats : List (ℕ × ℕ))
    (lo : List (OracleShape × ℕ)) (ps : List P5T.PSeat) (l : ℕ)
    (hT : bookedAllB Ld (N.msgsAt p) seats lo ps l = true) :
    ∀ i : Fin lo.length,
      seatBy noFirst s.book (noK10 seats lo ps l i) = some (seatK10 lo ps l i) := by
  intro i
  have h := List.all_eq_true.1 hT i.val (List.mem_range.2 i.isLt)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  exact seat_at_book hbook hseats hord hb _ _ h.1 h.2

/-! ## The test can say no -/

/-- Two entries of link 0, each with a sample, at the seats (0, 0) and (1, 0). -/
def psToy : List P5T.PSeat :=
  [{ label := "a", send := 0, seg := some (0, 0), idx := 0, j := 0, t := 0,
     shape := { (default : OracleShape) with answers := 1 }, role := .other },
   { label := "b", send := 1, seg := some (0, 1), idx := 0, j := 1, t := 0,
     shape := { (default : OracleShape) with answers := 1 }, role := .other }]

theorem bookedAllB_yes : bookedAllB { places := [(0, 0), (1, 0)] } 2 [(0, 0), (1, 0)]
    [(default, 7), (default, 7)] psToy 0 = true := by decide +kernel

theorem bookedAllB_late : bookedAllB { places := [(0, 0), (1, 0)] } 1 [(0, 0), (1, 0)]
    [(default, 7), (default, 7)] psToy 0 = false := by decide +kernel

theorem bookedAllB_place : bookedAllB { places := [(0, 0), (2, 0)] } 2 [(0, 0), (1, 0)]
    [(default, 7), (default, 7)] psToy 0 = false := by decide +kernel

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.noK10_is
#print axioms VerifiableInference.Desc.First.Close.seat_at_book
#print axioms VerifiableInference.Desc.First.Close.hs_k10
#print axioms VerifiableInference.Desc.First.Close.bookedAllB_yes
#print axioms VerifiableInference.Desc.First.Close.bookedAllB_late
#print axioms VerifiableInference.Desc.First.Close.bookedAllB_place
