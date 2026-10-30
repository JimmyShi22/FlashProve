-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Door/DoorGives.lean: **WHAT THE DOOR's BOOLS' YES GIVES**, in plain sentences on
the
record, for whoever spends the items without the tree's forms. No Mathlib. Statements and proofs.
  `numbers_of_book`: "K12.bookInOrder" at ft: the tree at the book's place z bears the number ft +
    z; `numbers_of_book0`: at ft = 0: the number z.
  `roots_of_book`: and the record's count of roots is the book's number of trees.
  `place_of_seats`: "K12.seatsCarried": below the book's number of messages the place of message o
    is the plan's list's entry number o.
  `placesBelowB L n m`: A TEST WITH CODE ON THE PLAN's LIST: the first n places name trees below m.
  `place_in_book`: "K12.seatsCarried" · the book has a place for each of the statement's messages ·
    that test at the book's own two counts: THEN every message of the statement has a place, and the
    tree that it names is in the book.
  (`msgShape_at`: "K12.msgShapes": Johnson/Desc/K12/Door/MsgShapes.lean.)
Limits. Nothing on soundness. The two counts at which `placesBelowB` is asked are the record's: by
the table's fixed clause on the book they are the plan's numbers at the border.

-/
import Johnson.Desc.K12.Door.MsgShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Door
open OnBytes OnBytes.Params

theorem numbers_of_book {ft : Nat} {B : TreeBook} {roots : Nat}
    (h : bookInOrderB ft B roots = true) (z : Nat) (T : Tree) (hT : B.trees[z]? = some T) :
    T.number = ft + z := by
  unfold bookInOrderB at h
  rw [Bool.and_eq_true] at h
  have hz : z < B.trees.size := by
    rcases Nat.lt_or_ge z B.trees.size with h' | h'
    · exact h'
    · rw [Array.getElem?_eq_none h'] at hT
      cases hT
  have h1 := List.all_eq_true.1 h.2 z (List.mem_range.2 hz)
  rw [hT] at h1
  exact eq_of_beq h1

theorem numbers_of_book0 {B : TreeBook} {roots : Nat} (h : bookInOrderB 0 B roots = true) (z : Nat)
    (T : Tree) (hT : B.trees[z]? = some T) : T.number = z := by
  rw [numbers_of_book h z T hT, Nat.zero_add]

theorem roots_of_book {ft : Nat} {B : TreeBook} {roots : Nat}
    (h : bookInOrderB ft B roots = true) : roots = B.trees.size := by
  unfold bookInOrderB at h
  rw [Bool.and_eq_true] at h
  exact eq_of_beq h.1

theorem place_of_seats {L : Laid} {B : TreeBook} (h : seatsCarriedB L B = true) (o : Nat)
    (ho : o < B.place.size) : B.place[o]? = L.places[o]? := by
  unfold seatsCarriedB at h
  simp only [Bool.and_eq_true] at h
  have e : B.place.toList = L.places.take B.place.size := eq_of_beq h.1.1.1
  rw [← Array.getElem?_toList, e, List.getElem?_take_of_lt ho]

/-- The first n places of the plan's list name trees below m. -/
def placesBelowB (L : Laid) (n m : Nat) : Bool := (L.places.take n).all fun q => decide (q.1 < m)

theorem place_in_book {L : Laid} {B : TreeBook} {st : Statement} (h : seatsCarriedB L B = true)
    (hs : B.place.size = st.oracles.size) (hb : placesBelowB L B.place.size B.trees.size = true)
    (o : Nat) (ho : o < st.oracles.size) : ∃ q, B.place[o]? = some q ∧ q.1 < B.trees.size := by
  rw [← hs] at ho
  refine ⟨B.place[o], Array.getElem?_eq_getElem ho, ?_⟩
  have e1 := place_of_seats h o ho
  rw [Array.getElem?_eq_getElem ho] at e1
  have hm : B.place[o] ∈ L.places.take B.place.size := by
    have e2 : (L.places.take B.place.size)[o]? = some B.place[o] := by
      rw [List.getElem?_take_of_lt ho, ← e1]
    exact List.mem_of_getElem? e2
  exact of_decide_eq_true (List.all_eq_true.1 hb _ hm)

end VerifiableInference.Desc.K12.Door

#print axioms VerifiableInference.Desc.K12.Door.numbers_of_book0
#print axioms VerifiableInference.Desc.K12.Door.place_of_seats
#print axioms VerifiableInference.Desc.K12.Door.place_in_book
