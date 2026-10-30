-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05OwnersGive.lean: kind K5: THE KIND's TWO BOOLS ON THE SEATS AND THE SHAPES
OF THE MESSAGES THAT ARE READ (seatsOnB, shapesOnB, Johnson/Desc/First/Att/K05DoorB.lean) FROM THE
TWO BOOLS OF THE ITEMS' OWNER THAT ARE OPEN AT THE SAME BORDER ("K12.seatsCarried": seatsCarriedB,
Johnson/Desc/K12/Door/DoorBools.lean; "K12.msgShapes": msgShapesB,
Johnson/Desc/K12/Door/MsgShapes.lean).

THE OWNER's BOOLS DO NOT GIVE THE KIND's ALONE. The owner's speak by the message's number in the
statement; the kind's by the member's number in the caller's list, which the live request's frame
turns into a number in the statement (oracleOfMsg). Which numbers the frame holds is asked here as a
premise, member by member.

IS IT EMPTY HERE? At the empty list of pairs both conclusions hold where a link is open. NO MEMBER
IS SHOWN.

Main names:
  `seatsOn_of_carried`: seatsOnB, from seatsCarriedB and, for each pair (k, seat): the frame has
    member k under a number o; o is below the book's number of places; the plan's list has that seat
    at o; the seat lies in own.
  `shapesOn_of_msgShapes`: shapesOnB, from msgShapesB and, for each pair (k, shape): the frame has
    member k under a number o; o is below the statement's number of messages; the plan's list has
    that shape at o.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05DoorB
import Johnson.Desc.K12.Door.MsgShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K12.Door (Laid seatsCarriedB msgShapesB msgShape_at)

/-- What a yes of the owner's test on the seats gives at a number below the book's. -/
theorem place_at {Ld : Laid} {B : TreeBook} (h : seatsCarriedB Ld B = true) (o : Nat)
    (ho : o < B.place.size) : B.place[o]? = Ld.places[o]? := by
  unfold seatsCarriedB at h
  simp only [Bool.and_eq_true] at h
  have e : B.place.toList = Ld.places.take B.place.size := eq_of_beq h.1.1.1
  rw [← Array.getElem?_toList, e, List.getElem?_take_of_lt ho]

/-- **The kind's Bool on the seats, from the owner's.** -/
theorem seatsOn_of_carried {Ld : Laid} {s : First.S} {L : LinkCtx} {kept : Nat}
    {pairs : List (Nat × (Nat × Nat))} {own : List (Nat × Nat)}
    (h : seatsCarriedB Ld s.book = true) (hL : s.link? = some L)
    (hp : ∀ p ∈ pairs, ∃ o, oracleOfMsg L.check.frame kept p.1 = some o ∧ o < s.book.place.size ∧
      Ld.places[o]? = some p.2 ∧ own.contains p.2 = true) :
    seatsOnB kept pairs own s = true := by
  unfold seatsOnB
  rw [hL]
  show (pairs.all fun x => _) = true
  refine List.all_eq_true.2 fun p hpm => ?_
  obtain ⟨o, e1, e2, e3, e4⟩ := hp p hpm
  rw [e1]
  show (s.book.place[o]? == some p.2 && own.contains p.2) = true
  rw [place_at h o e2, e3, e4]
  simp

/-- **The kind's Bool on the shapes, from the owner's.** -/
theorem shapesOn_of_msgShapes {M : List OracleShape} {s : First.S} {L : LinkCtx} {kept : Nat}
    {pairs : List (Nat × OracleShape)} (h : msgShapesB M s.st = true) (hL : s.link? = some L)
    (hp : ∀ p ∈ pairs, ∃ o, oracleOfMsg L.check.frame kept p.1 = some o ∧ o < s.st.oracles.size ∧
      M[o]? = some p.2) :
    shapesOnB kept pairs s = true := by
  unfold shapesOnB
  rw [hL]
  show (pairs.all fun x => _) = true
  refine List.all_eq_true.2 fun p hpm => ?_
  obtain ⟨o, e1, e2, e3⟩ := hp p hpm
  rw [e1]
  show ((s.st.oracles[o]?).any fun y => y.shape == p.2) = true
  have e := msgShape_at h o e2
  rw [e3] at e
  obtain ⟨y, hy, hs⟩ := Option.map_eq_some_iff.1 e
  rw [hy]
  show (y.shape == p.2) = true
  rw [hs]
  exact beq_self_eq_true _

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.place_at
#print axioms VerifiableInference.Desc.First.Att.P.seatsOn_of_carried
#print axioms VerifiableInference.Desc.First.Att.P.shapesOn_of_msgShapes
