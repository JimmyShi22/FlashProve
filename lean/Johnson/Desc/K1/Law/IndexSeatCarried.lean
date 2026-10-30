-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/IndexSeatCarried.lean: WHAT "THE SEATS ARE CARRIED" (`K12.Coin.SeatsPrefix`,
Johnson/Desc/K12/Coin/BookRides.lean: the book's places are a prefix of the plan's list) GIVES: A
MESSAGE's SEAT;
AND THE INDEX MASKS' SEAT IN FIVE STEPS. Two statements with their proofs. No statement here names
the table of joints.
  `seat_of_carried`: a place that the book has is the plan's.
  `indexSeat_of_carried`: **the five steps**: the seats are carried · the book has a place for every
    message · the index masks' message is there · its number is n · the plan's list has seat at n:
    so by the book that message sits at seat (`indexSeatB`, Johnson/Desc/K1/Law/IndexBools.lean).
What is not claimed. Any of the five. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.IndexBools
import Johnson.Desc.K12.Coin.BookRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12.Coin (SeatsPrefix)

/-- **What "the seats carried" gives**: a place that the book has is the plan's. -/
theorem seat_of_carried {L : K12.Coin.Laid} {B : TreeBook} (h : SeatsPrefix L B) {i : Nat}
    (hi : i < B.place.size) {seat : Nat × Nat} (hL : L.places[i]? = some seat) :
    B.place[i]? = some seat := by
  rw [← Array.getElem?_toList, h.1, List.getElem?_take_of_lt hi]
  exact hL

/-- **THE FIVE STEPS**: the index masks' seat. -/
theorem indexSeat_of_carried {L : K12.Coin.Laid} {s : S} {n : Nat} {seat : Nat × Nat}
    (h1 : SeatsPrefix L s.book) (h2 : s.book.place.size = s.st.oracles.size)
    (h3 : indexThereB s = true) (h4 : indexIsB n s = true) (h5 : L.places[n]? = some seat) :
    indexSeatB seat s = true := by
  unfold indexIsB at h4
  rw [beq_iff_eq] at h4
  unfold indexThereB at h3
  have hlt : s.out.indexMasks < s.st.oracles.size := by
    by_contra hn
    rw [Array.getElem?_eq_none (by omega)] at h3
    cases h3
  unfold indexSeatB
  rw [seat_of_carried h1 (by omega) (by rw [h4]; exact h5)]
  exact beq_self_eq_true _

end VerifiableInference.Desc.K1
