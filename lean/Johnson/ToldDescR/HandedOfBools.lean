-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/HandedOfBools.lean: no soundness is claimed.
The spending of four tests with code on the first chain's last state, said of the state alone: whoever holds the tests' accepts may call these, wherever the accepts come from: a public item of the first table's promise (as HandedAtEnd.lean and HandedTwo.lean have it) or a field of the fold's facts at a reached state (stated, not shown here: the names «K12.bookInOrder» · «K12.bookFits» · «K13.ownSits» leave the table's door).
  **handedRoots_of_bools**  firstOfS s = some f · bookInOrderB ft s.book s.roots · s.book.trees.size = n₁ ⇒ f.roots = n₁ ∧ ∀ j T, f.book.trees[j]? = some T → T.number = ft + j  (the first two clauses of HandedRoots)
  **handedTwo_of_bools**    firstOfS s = some f · ownSitsB V s · bookFitsB s.book · bookInOrderB 0 s.book s.roots ⇒ HandedTwo V.index V.w V.indexShape V.wShape f
No member. Nothing on soundness.
-/
import Johnson.ToldDescR.HandedTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third (firstOfS)
open VerifiableInference.Desc.K12.Door (bookInOrderB numbers_of_book roots_of_book)

theorem handedRoots_of_bools {s : First.S} {f : Handed} (hf : firstOfS s = some f) {ft n₁ : ℕ}
    (hb : bookInOrderB ft s.book s.roots = true) (hn : s.book.trees.size = n₁) :
    f.roots = n₁ ∧ ∀ (j : ℕ) (T : Tree), f.book.trees[j]? = some T → T.number = ft + j := by
  unfold firstOfS at hf
  obtain ⟨e, _, rfl⟩ := Option.map_eq_some_iff.1 hf
  exact ⟨(roots_of_book hb).trans hn, fun j T hT => numbers_of_book hb j T hT⟩

theorem handedTwo_of_bools {s : First.S} {f : Handed} (hf : firstOfS s = some f) {V : OwnSeats}
    (hS : ownSitsB V s = true) (hF : bookFitsB s.book = true)
    (hb : bookInOrderB 0 s.book s.roots = true) :
    HandedTwo V.index V.w V.indexShape V.wShape f := by
  have h1 := (ownSitsB_iff V s).1 hS f hf
  obtain ⟨-, hN⟩ := handedRoots_of_bools hf hb rfl
  have hF' : VerifiableInference.Desc.Book.BookFits f.book := by
    unfold firstOfS at hf
    obtain ⟨e, _, rfl⟩ := Option.map_eq_some_iff.1 hf
    exact (bookFitsB_iff _).1 hF
  exact handedTwo_of_sits h1 hF' fun j T hT => by rw [hN j T hT, Nat.zero_add]

end ToldDesc

#print axioms ToldDesc.handedRoots_of_bools
#print axioms ToldDesc.handedTwo_of_bools
