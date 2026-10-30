-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/IndexBools.lean: FOUR TESTS WITH CODE ON THE FIRST CHAIN's RECORD, meant for the
sentences of three public items of the table of joints (Johnson/Desc/First/Borders.lean:
`Pub.noneSent`, `Pub.indexIs`, `Pub.indexThere`); THEIR MAKER: the block named "G0:1"
(`openingZero`, Johnson/Desc/K1/Law/OpeningZero.lean); AND THE SENDING KIND's KEEPING OF THE LAST
THREE. Four definitions, and statements with their proofs. No statement here names the table.
Main names:
  `noneSentB s`: no oracle message stands in the statement, and nothing is laid "at the start".
  `indexIsB n s`: the record's number of the index masks' message is n.
  `indexThereB s`: the statement holds a message of the record's number.
  `indexSeatB seat s`: BY THE RECORD's OWN BOOK THE MESSAGE OF THAT NUMBER SITS AT seat (a tree and
    a place in it). Why: the rows on the table name their mask entries by the NUMBER; a pin speaks
    of a TENANT; a reader that goes from the one to the other by the book is fixed by the pin only
    where this holds.
  `openingZero_makes`: **the maker**: from a record that passes `noneSentB`, behind a yes of the
    joined block: `indexIsB ((firstPar q gp).sent.size - 1)` and `indexThereB` say yes: the index
    masks' message is the last that the block sends.
  `openingZero_seat`: **the seat's maker**: from such a record, whose book holds no place: the seat
    is (the book's trees in front + `(layOf P).tree (n - 1)`, `(layOf P).part (n - 1)`), P the
    opening's place, n the number of its messages: by `Booked.newer`.
  `Booked.seat_kept`, `sendAtS_index`: **kept**: W's sending leaves "out", the older messages and
    the older places (`Booked.older`).
  `noneSentB_behind`: a try: behind that yes `noneSentB` says no (so the item is rightly dropped
    there).

What is not claimed. That the first record passes `noneSentB`, or that its book is empty. That a
table's `Numbers.indexNo` is (firstPar q gp).sent.size - 1, or its `Numbers.index` the seat made
here: equations on the plan. That other kinds' blocks keep the three. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.OpeningZero
import Johnson.Desc.K1.Law.KeptAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk (LayPar)

variable {Cl : Type}

/-- No oracle message stands in the statement, and nothing is laid "at the start". -/
def noneSentB (s : S) : Bool := s.st.oracles.isEmpty && s.check.frame.atStart.isEmpty

/-- The record's number of the index masks' message is n. -/
def indexIsB (n : Nat) (s : S) : Bool := s.out.indexMasks == n

/-- The statement holds a message of the record's number. -/
def indexThereB (s : S) : Bool := (s.st.oracles[s.out.indexMasks]?).isSome

/-- By the record's own book the message of the record's number sits at seat. -/
def indexSeatB (seat : Nat × Nat) (s : S) : Bool :=
  s.book.place[s.out.indexMasks]? == some seat

/-- **THE MAKER.** -/
theorem openingZero_makes {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
    {fvs : List Bool} {kCol : Nat} {s t : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t)
    (h0 : noneSentB s = true) :
    indexIsB ((firstPar q gp).sent.size - 1) t = true ∧ indexThereB t = true := by
  unfold noneSentB at h0
  rw [Bool.and_eq_true, Array.isEmpty_iff, Array.isEmpty_iff] at h0
  have hi := openingZero_index h h0.2
  rw [h0.1] at hi
  refine ⟨?_, (openingZero_rec h).2.2.2.2.2.2⟩
  unfold indexIsB
  rw [beq_iff_eq]
  have : (#[] : Array OnBytes.Oracle).size = 0 := rfl
  omega

/-- **THE SEAT's MAKER.** -/
theorem openingZero_seat {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
    {fvs : List Bool} {kCol : Nat} {s t : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t)
    (h0 : noneSentB s = true) (hb : s.book.place.size = s.st.oracles.size) :
    indexSeatB (s.book.trees.size +
        (layOf (firstPar q gp)).tree.getD ((firstPar q gp).sent.size - 1) 0,
      (layOf (firstPar q gp)).part.getD ((firstPar q gp).sent.size - 1) 0) t = true := by
  have hi := (openingZero_makes h h0).1
  unfold indexIsB at hi
  rw [beq_iff_eq] at hi
  have hB := (openingZero_rec h).2.2.2.2.1
  have hthere := (openingZero_rec h).2.2.2.2.2.2
  unfold noneSentB at h0
  rw [Bool.and_eq_true, Array.isEmpty_iff, Array.isEmpty_iff] at h0
  have hz : s.st.oracles.size = 0 := by rw [h0.1]; rfl
  have hpos : 0 < (firstPar q gp).sent.size := by
    by_contra hn
    have hm := hB.msgs
    rw [Array.getElem?_eq_none (by omega)] at hthere
    cases hthere
  have hp := hB.newer hb (i := (firstPar q gp).sent.size - 1) (by omega)
  unfold indexSeatB
  rw [hi]
  rw [hz, Nat.zero_add] at hp
  rw [hp]
  exact beq_self_eq_true _

/-- **Kept by a sending**: the older places stay. -/
theorem Booked.seat_kept {P : Par} {bk bk' : TreeBook} {n n' i : Nat} {seat : Nat × Nat}
    (h : Booked P bk n bk' n') (hs : bk.place[i]? = some seat) : bk'.place[i]? = some seat := by
  have hi : i < bk.place.size := by
    by_contra hn
    rw [Array.getElem?_eq_none (by omega)] at hs
    cases hs
  rw [h.older hi]
  exact hs

/-- W's sending keeps the three. -/
theorem sendAtS_index (P : Par) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (sendAtS P : Block S Cl).decide s [r₁, r₂] gs = .ok s') (n : Nat) (seat : Nat × Nat) :
    (indexIsB n s = true → indexIsB n s' = true) ∧
      (indexThereB s = true → indexThereB s' = true) ∧
      (indexSeatB seat s = true → indexSeatB seat s' = true) := by
  obtain ⟨_, _, _, _, ho⟩ := sendAtS_ok P s s' _ gs h
  have hk := (sendAtS_kept P s s' _ gs h).2.2
  have hb := sendAtS_booked P s s' r₁ r₂ gs h
  unfold indexIsB indexThereB indexSeatB
  rw [ho]
  refine ⟨id, fun h1 => ?_, fun h1 => ?_⟩
  · have hlt : s.out.indexMasks < s.st.oracles.size := by
      by_contra hn
      rw [Array.getElem?_eq_none (by omega)] at h1
      cases h1
    rw [hk _ hlt]
    exact h1
  · rw [beq_iff_eq] at h1 ⊢
    exact hb.seat_kept h1

/-- A try: behind that yes a message stands in the statement. -/
theorem noneSentB_behind {q : Params.First} {gp : GPar} {nm : String} {X : LayPar}
    {fvs : List Bool} {kCol : Nat} {s t : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t) :
    noneSentB t = false := by
  have hs := (openingZero_rec h).2.2.2.2.2.2
  unfold noneSentB
  rw [Bool.and_eq_false_iff]
  left
  rw [← Bool.not_eq_true, Array.isEmpty_iff]
  intro e
  rw [e] at hs
  cases hs

end VerifiableInference.Desc.K1
