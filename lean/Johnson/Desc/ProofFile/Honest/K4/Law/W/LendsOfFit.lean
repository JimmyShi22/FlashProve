-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/LendsOfFit.lean: statements with their proofs; the second is
CONDITIONAL.

What is here. THE FIELD lends OF THE PUBLIC TEST `K4LastEntry` (Law/W/LastEntry.lean), THAT THE
BOOK LENDS THE PUBLIC ROW OF THE MEMBER OF THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4),
FROM WHAT IS LEFT OF IT once the book's own tests have paid the cuts (`lendsRow_of_fit`,
Honest/Small/LendsRowOf.lean, over Honest/BookLends.lean of other writers).

  `k4Row_plain`   **every part of K4's row takes no coin of its own and carries none**: no
      hypothesis.
  `k4_lends_of_fit`   **lends**, from: the book passes its own tests (h) · the library's test on
      places (hp) · K4's place is a place of the first chain (ha) · the book's first table has no
      row at an address of K4's parts (hd) · the book has no carried entry for them (hca) · hsp.

hsp IS WHERE K4's OWN DEBT SITS: ONE EQUATION OF PUBLIC LISTS A PART: THE NAMES AND COUNTS OF THE
BOOK's SPENDING ENTRIES FOR PART NUMBER i OF K4's PLACE, IN THE BOOK's ORDER, ARE WHAT THAT PART
STATES THAT IT SPENDS. No fact on the book alone gives it. IT IS NOT SHOWN AT ANY BOOK OF THE
FULL SIZE. TWO EDGES AT A COUNT 0: a part for scalars that states a run of count 0, and a masked
sumcheck that states end values of number 0, state a run for which a book's maker may lay no entry:
there hsp is false. AND A THIRD, THE OTHER WAY ROUND: a maker may lay an entry of count 0 (for a
masked sumcheck with end values, a merge or not, all of whose scalars are end values): there hsp
wants that the part states a run of count 0. THE RULE FOR A PART THAT WOULD MEET THE BOOK: state no
run where the maker lays none; state a run of count 0 where it lays one.

Not shown here. That any book meets h; hp; ha; hd; hca; hsp. What is lent is not described. At
chain number 0 alone. Nothing on soundness, on completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.Small.LendsRowOf
import Johnson.Desc.ProofFile.Honest.K4.Law.SlotsTrue

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.W
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (FileDescription Place)

/-- **EVERY PART OF K4's ROW TAKES NO COIN OF ITS OWN AND CARRIES NONE.** No hypothesis. -/
theorem k4Row_plain (Q : K4Pub) : ∀ p ∈ k4RowIn Q, p.takes = ⟨0, 0⟩ ∧ p.carries = [] := by
  intro p hp
  rw [k4RowIn_all] at hp
  rcases List.mem_append.1 hp with h | h
  · rw [List.eq_of_mem_replicate h]
    exact ⟨rfl, rfl⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals first
      | (subst h; exact ⟨rfl, rfl⟩)
      | (subst h; split <;> exact ⟨rfl, rfl⟩)

variable {Xi : Type} {F : FileDescription Xi} {B : ProverCoinCounts}

/-- CONDITIONAL on h, hp, ha, hd, hca and hsp. **THE BOOK LENDS K4's PUBLIC ROW.** -/
theorem k4_lends_of_fit (h : B.word F = none) (hp : F.placesOk = true) {Q : K4Pub}
    (ha : k4Place Q ∈ placesAt F 0)
    (hd : ∀ i, i < (k4RowIn Q).length → dueAt (B.rowsOf 0) ⟨k4Place Q, i⟩ = ⟨0, 0⟩)
    (hca : ∀ i, i < (k4RowIn Q).length → carryE B ⟨k4Place Q, i⟩ = [])
    (hsp : ∀ i p, (k4RowIn Q)[i]? = some p →
      (spentE B ⟨k4Place Q, i⟩).map Ahead.named = p.spends) :
    lendsRow B 0 (k4Place Q) (k4RowIn Q) = true := by
  refine lendsRow_of_fit h hp (Or.inl rfl) ha (k4RowIn Q) fun i p hq => ?_
  obtain ⟨hi, e⟩ := List.getElem?_eq_some_iff.1 hq
  obtain ⟨t, c⟩ := k4Row_plain Q p (List.mem_of_getElem? hq)
  refine ⟨?_, hsp i p hq, ?_⟩
  · rw [t, hd i hi]
  · rw [c, hca i hi]
    rfl

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4Row_plain
#print axioms ProofFile.Honest.K4.W.k4_lends_of_fit
