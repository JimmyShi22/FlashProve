-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/BookRawShared.lean: THE FRAME's bookWhole_ahead_shared
(Honest/BookSharedLaw.lean) AT THE RAW BOOK: at an owner that stands at no place of the first or the
second chain the entries of the book that bookRaw returns (Honest/BookWhole.lean: the book BEFORE
ITS OWN TESTS ARE ASKED) are those of the short list sharedAhead (Honest/BookShared.lean), in the
same order. One statement with its proof; no definition. No kind's part is named.

  bookRaw_ahead_shared   the statement

Whose text. THE PROOF IS THE FRAME's OWN: the steps of bookWhole_ahead_shared behind its third line,
where it has passed from the whole book to the raw one (checked_ok); typed once more because they
stand inside that proof and cannot be called. The frame's statement follows from this one and
checked_ok. All lemmas called are the frame's (Honest/BookSharedKit.lean,
Honest/BookSharedLaw.lean).
What it is for. A statement on a test at the raw book bears in its type that none of the book's own
tests is used.
What is not claimed. That bookRaw returns at any file. No property.
-/
import Johnson.Desc.ProofFile.Honest.BookSharedLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (FileDescription)
open ProofFile.Honest.BookShared

/-- **At an owner that stands at no place of the first or the second chain the raw book's entries
are sharedAhead's**, in the same order. -/
theorem bookRaw_ahead_shared {Xi : Type} {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends}
    {M : Merges} {W : ProverCoinCounts} (hW : bookRaw F p0 p1 p2 M = .ok W) :
    ∃ l, sharedAhead F p1 = .ok l ∧
      ∀ o : Addr, o.place ∉ F.first.blocksInOrder.map (·.place) → o.place ∉ F.second.blocksInOrder.map (·.place) →
        W.ahead.filter (·.owner == o) = l.filter (·.owner == o) := by
  obtain ⟨B₀, m0, m1, seg, cF, cO, iF, iO, pq, tail, hB, hm0, hm1, hseg, hiF, hcF, hiO, hcO, hpq,
    htail, eW⟩ := bookRaw_ahead hW
  obtain ⟨ws, f0, f1, f2, hws, hf0, hf1, hf2, eB⟩ := spendingBook_ahead hB
  refine ⟨f1 ++ (splitEntry F.shared.blocksInOrder p1).toList ++ cF ++ cO ++
    carryPair pq.1 pq.2 ((under m1 "Omega").filter (!·.masks)) none ++
    (ownFreshIn F.shared.blocksInOrder).map (·.carry tail), ?_, ?_⟩
  · unfold sharedAhead
    refine bind_of_ok hf1 ?_
    refine bind_of_ok hm1 ?_
    refine bind_of_ok hiF ?_
    refine bind_of_ok hcF ?_
    refine bind_of_ok hiO ?_
    refine bind_of_ok hcO ?_
    refine bind_of_ok hpq ?_
    refine bind_of_ok htail ?_
    rfl
  · intro o h1 h3
    have ne1 : ∀ a : Addr, a.place ∈ F.first.blocksInOrder.map (·.place) → a ≠ o :=
      fun a ha e => h1 (e ▸ ha)
    have ne3 : ∀ a : Addr, a.place ∈ F.second.blocksInOrder.map (·.place) → a ≠ o :=
      fun a ha e => h3 (e ▸ ha)
    have s0 : ∀ m ∈ m0, m.sender ≠ o := fun m hm => ne1 _ (sentIn_sender hm0 m hm)
    have z1 : (ws.map (·.entry)).filter (·.owner == o) = [] := filter_none (by
      intro e he
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 he
      exact ne1 _ (hws w hw))
    have z2 : f0.filter (·.owner == o) = [] := filter_none (by
      intro e he
      refine ne1 e.owner ?_
      rw [← planOf_places F.first.blocksInOrder]
      exact foldEntries_owner hf0 e he)
    have z3 : f2.filter (·.owner == o) = [] := filter_none (by
      intro e he
      refine ne3 e.owner ?_
      rw [← planOf_places F.second.blocksInOrder]
      exact foldEntries_owner hf2 e he)
    have z4 : seg.filter (·.owner == o) = [] := filter_none (by
      intro e he
      obtain ⟨m, hm, hom⟩ := segmentCarries_owner hseg e he
      rw [hom]
      exact s0 m hm)
    have z5 := carryPair_filter (p := pq.1) (q := pq.2) (o := o)
      (R₁ := m0.filter (·.masks) ++ (under m0 "W").filter (!·.fresh))
      (R₂ := (under m1 "Omega").filter (!·.masks)) (own := (under m0 "W").find? (·.fresh))
      (by
        intro m hm
        rcases List.mem_append.1 hm with h4 | h4
        · exact s0 m (List.mem_filter.1 h4).1
        · exact s0 m (List.mem_filter.1 (List.mem_filter.1 h4).1).1)
      (by
        intro m hm
        exact s0 m (List.mem_filter.1 (List.mem_of_find?_eq_some hm)).1)
    rw [eW, eB]
    simp only [List.filter_append]
    rw [z5]
    simp only [z1, z2, z3, z4, List.nil_append, List.append_assoc]

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.bookRaw_ahead_shared
