-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/BookFactsOfTests.lean: AT ANY STATE OF THE FIRST CHAIN: TWO TESTS WITH CODE ON
THE BOOK OF TREES, AND "AS MANY PLACES AS ORACLE MESSAGES", GIVE THE TWO FACTS ON THE BOOK THAT THE
SHARED TABLE's CONSTANT SPENDS. A theorem.
  `bookFacts_of_tests`: from `K12.Door.atFirstBook 0 s` (every tree of the book bears its place as
    its number; as many roots as trees), `Sound.bookFitsB s.book` (each place of the book names a
    tree that is there, which holds that message at that tenant) and
    `s.book.place.size = s.st.oracles.size`: (1) every tree of the book bears its own place as its
    number; (2) every oracle message of the statement has a place in the book, at a tree that is
    there.
The sentence reads one state: it names no item of the table's door and no filling. By unfolding the
two tests.
What is not claimed. The three premises at any state. Without the third the sentence is false by its
form (the two tests read the book alone). Nothing on soundness.

-/
import Johnson.Desc.K12.Door.DoorBools
import Johnson.Desc.Sound.BookTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K14.Law
open OnBytes

/-- **The two tests on the book and the equal counts give the two facts on the book.** -/
theorem bookFacts_of_tests (s : First.S) (h1 : K12.Door.atFirstBook 0 s = true)
    (h2 : Sound.bookFitsB s.book = true) (h3 : s.book.place.size = s.st.oracles.size) :
    (∀ (z : Nat) (T : Tree), s.book.trees[z]? = some T → T.number = z) ∧
      ∀ o, o < s.st.oracles.size →
        ∃ q : Nat × Nat, s.book.place[o]? = some q ∧ q.1 < s.book.trees.size := by
  refine ⟨fun z T hz => ?_, fun o ho => ?_⟩
  · unfold K12.Door.atFirstBook K12.Door.bookInOrderB at h1
    have h := (Eq.mp (Bool.and_eq_true _ _) h1).2
    have hlt : z < s.book.trees.size := (Array.getElem?_eq_some_iff.1 hz).1
    have hz' := List.all_eq_true.1 h z (List.mem_range.2 hlt)
    rw [hz] at hz'
    simpa using hz'
  · have hlt : o < s.book.place.size := by
      rw [h3]
      exact ho
    have hq : s.book.place[o]? = some s.book.place[o] := Array.getElem?_eq_getElem hlt
    refine ⟨_, hq, ?_⟩
    unfold Sound.bookFitsB at h2
    have h := List.all_eq_true.1 h2 o (List.mem_range.2 hlt)
    rw [hq] at h
    cases ht : s.book.trees[(s.book.place[o]).1]? with
    | none =>
      simp only [ht] at h
      cases h
    | some t => exact (Array.getElem?_eq_some_iff.1 ht).1

end VerifiableInference.Desc.K14.Law

#print axioms VerifiableInference.Desc.K14.Law.bookFacts_of_tests
