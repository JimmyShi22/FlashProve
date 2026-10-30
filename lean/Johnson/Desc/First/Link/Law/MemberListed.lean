-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/MemberListed.lean: AT A REACHED STATE WITH THE PROMISE's `bookAt`: WHERE
THE BOOK PLACES MESSAGE o AT A SEAT q OF own, A MEMBER OF ms SITS AT q, AND ITS SHAPE IS THE LISTED
SHAPE OF MESSAGE o. From one field of the list of lemmas along "reached" (`FoldFacts.seatsCarried`)
and one test with code on public data. For the third tie at the one equation's piece.

What is said.
  `place_listed`: the book's place of a message is the listed one (`d.L.places`).
  `membersThereB d ms own n`: at every o below n whose listed seat is of own: ms has a member at
that
    seat and the member's shape is `d.M[o]`.
  `member_listed`: **the sentence above.**

Limits. The test has run at no data here. No soundness statement.

-/
import Johnson.Desc.First.FoldFacts
import Johnson.Desc.Sound.World

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Sound (Mem seatOf)
open VerifiableInference.Desc.First (S ModelPart Numbers FoldData FoldFacts bookAt)

/-- **The book's place of a message is the listed one.** -/
theorem place_listed {X P : Type} {Rch : ℕ → X → Prop} {at_ : X → P × S} {d : FoldData}
    {reqW : P → Array UInt32} {links : List ModelPart} {ps : List Place}
    (FF : FoldFacts Rch at_ d reqW links ps) {k : ℕ} {a : X} (hR : Rch k a)
    (hu : (at_ a).2.failed = none) {o : ℕ} {q : ℕ × ℕ}
    (hq : (at_ a).2.book.place[o]? = some q) : d.L.places[o]? = some q := by
  have hS := FF.seatsCarried k a hR hu
  unfold K12.Door.atFirstSeats K12.Door.seatsCarriedB at hS
  simp only [Bool.and_eq_true, beq_iff_eq] at hS
  have e0 : (at_ a).2.book.place.toList = d.L.places.take (at_ a).2.book.place.size := hS.1.1.1
  have h3 : (at_ a).2.book.place.toList[o]? = some q := by
    rw [Array.getElem?_toList]
    exact hq
  rw [e0, List.getElem?_take] at h3
  split at h3
  · exact h3
  · cases h3

/-- On public data alone: the members are there, with the listed shapes. -/
def membersThereB (d : FoldData) (ms : List Mem) (own : List (ℕ × ℕ)) (n : ℕ) : Bool :=
  (List.range n).all fun o =>
    match d.L.places[o]? with
    | some x =>
      !own.contains x ||
        match ms.find? fun y => decide (seatOf y = x) with
        | some y => decide (d.M[o]? = some (y.1.l.get y.2).1)
        | none => false
    | none => true

/-- **A MEMBER SITS THERE, WITH THE LISTED SHAPE.** -/
theorem member_listed {X P : Type} {Rch : ℕ → X → Prop} {at_ : X → P × S} {d : FoldData}
    {reqW : P → Array UInt32} {links : List ModelPart} {ps : List Place}
    (FF : FoldFacts Rch at_ d reqW links ps) (N : Numbers) (ms : List Mem) (own : List (ℕ × ℕ))
    {k : ℕ} {a : X} (hR : Rch k a) (hu : (at_ a).2.failed = none)
    (hB : bookAt N ps[k]? (at_ a).2 = true) {o : ℕ} {q : ℕ × ℕ}
    (hq : (at_ a).2.book.place[o]? = some q) (hown : own.contains q = true)
    (T : membersThereB d ms own (N.msgsAt ps[k]?) = true) :
    ∃ y, (ms.find? fun y => decide (seatOf y = q)) = some y ∧
      d.M[o]? = some (y.1.l.get y.2).1 := by
  have hlt : o < N.msgsAt ps[k]? := by
    unfold bookAt at hB
    simp only [Bool.and_eq_true, beq_iff_eq] at hB
    rw [← hB.2, ← hB.1.2]
    exact (Array.getElem?_eq_some_iff.1 hq).1
  have h1 := List.all_eq_true.1 T o (List.mem_range.2 hlt)
  simp only [place_listed FF hR hu hq, hown, Bool.not_true, Bool.false_or] at h1
  cases hy : ms.find? fun y => decide (seatOf y = q) with
  | none =>
    rw [hy] at h1
    cases h1
  | some y =>
    rw [hy] at h1
    exact ⟨y, rfl, of_decide_eq_true h1⟩

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.place_listed
#print axioms VerifiableInference.Desc.LinkJoin.member_listed
