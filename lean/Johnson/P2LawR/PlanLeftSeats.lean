-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/PlanLeftSeats.lean: A TEST WITH CODE, WITH ITS LAW, FOR THE LAST TABLE's TEST ON THE
PLAN "seats" (Johnson/LLT25R/LastLedger.lean: LastPlan8.seats : SeatsFit cs G mine; SeatsFit:
Johnson/Desc/Sound/WordsLaw.lean). So that whoever evaluates the test evaluates the field
itself. STATED AND PROVED: CALLS of the library's own test seatsFitB (Johnson/Desc/PlanMem.lean) and
of the law on it (Johnson/Top/H0/K2Caller/SeatFitsB.lean: seatFits_of_stretch). GENERAL
IN EVERY LETTER: no fixed value stands here.
WHAT THE FIELD READS. SeatsFit cs G mine says, of each x of mine, SeatFits G cs x.1.l x.1.seat: THE
WHOLE SENDING OF x: every member of the list x.1.l, not x's own place x.2 alone. SO A TEST WITH "A
MEMBER AN ENTRY" (the one shape and the one seat of x) READS LESS THAN THE FIELD wherever a sending
has more than one sampled member. The library's lists have one entry a SENDING: so has this test.
  entryOf s     a sending as the library's entry: its list of shapes with radii, and its seats by
                place (List.ofFn s.seat).
  seat_at · shape_at   the entry's seat and shape number i are the sending's.
  seatsB G cs mine   the library's seatsFitB at the entries of mine's sendings.
  **seatsB_law**   its yes gives SeatsFit cs G mine: the field's text.
  seatFits_of_entry   the same at one sending that stands among any lists L.
Limits. One way alone: from the test's yes to the field. A law of that form is empty where the test
never says yes: NO VALUE IS EVALUATED HERE. A sending that several of mine share is tested once a
member: no harm, some cost. Nothing on soundness or on hiding.

-/
import Johnson.Top.H0.K2Caller.SeatFitsB
import Johnson.Desc.Sound.WordsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.PlanLeft
open VerifiableInference.Desc (FileDescription MemberLists seatsFitB)
open VerifiableInference.Desc.Sound (Sending Mem SeatFits SeatsFit)
open VerifiableInference.Desc.First.K2Caller (seatFits_of_stretch)

/-- A sending as the library's entry. -/
def entryOf (s : Sending) : List (OnBytes.OracleShape × ℕ) × List (ℕ × ℕ) :=
  (s.l, List.ofFn s.seat)

/-- The entry's seat number i is the sending's. -/
theorem seat_at (s : Sending) (i : Fin s.l.length) :
    (entryOf s).2[0 + i.val]? = some (s.seat i) := by
  have hlt : i.val < (List.ofFn s.seat).length := by
    rw [List.length_ofFn]
    exact i.isLt
  rw [Nat.zero_add]
  show (List.ofFn s.seat)[i.val]? = some (s.seat i)
  rw [List.getElem?_eq_getElem hlt, List.getElem_ofFn]

/-- The entry's shape number i is the sending's. -/
theorem shape_at (s : Sending) (i : Fin s.l.length) :
    ∃ x, (entryOf s).1[0 + i.val]? = some x ∧ x.1 = (s.l.get i).1 := by
  refine ⟨s.l.get i, ?_, rfl⟩
  rw [Nat.zero_add]
  exact List.getElem?_eq_getElem i.isLt

variable {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes)

/-- One sending that stands among the lists. -/
theorem seatFits_of_entry {L : MemberLists} (h : seatsFitB G cs L = true) (s : Sending)
    (he : entryOf s ∈ L) : SeatFits G cs s.l s.seat :=
  seatFits_of_stretch G cs h he 0 s.l s.seat (shape_at s) (seat_at s)

/-- The field's test: the library's, at the entries of mine's sendings. -/
def seatsB (mine : List Mem) : Bool := seatsFitB G cs (mine.map fun x => entryOf x.1)

/-- **THE FIELD seats, IN ITS OWN TEXT, FROM THE TEST.** -/
theorem seatsB_law (mine : List Mem) (h : seatsB G cs mine = true) : SeatsFit cs G mine :=
  fun x hx => seatFits_of_entry G cs h x.1 (List.mem_map.2 ⟨x, hx, rfl⟩)

end P2Law.PlanLeft

#print axioms P2Law.PlanLeft.seat_at
#print axioms P2Law.PlanLeft.shape_at
#print axioms P2Law.PlanLeft.seatFits_of_entry
#print axioms P2Law.PlanLeft.seatsB_law
