-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Book/LastBook.lean: three facts on the book of commitment trees in a state of the first
chain, in the form in which the law of the last table's row 0 asks them (its premise hB), from two
tests with code on the book and "as many places as oracle messages". One definition, five theorems.
Joinings: no induction is typed here.

Why. The law of row 0's piece (Johnson/Flat/Last/RowZeroAtZ.lean) takes, of the first chain's last
state, under a condition Rc and "no mark": each tree's number is its place in the
book (`NumberedBook 0`); the book's two tables fit (`BookFits`); every oracle message of the
statement has a place in the book. Rc and the reader `get` are letters there.

What is said.
  `book_of_three`: at any state s: `K12.Door.atFirstBook 0 s = true`, `bookFitsB s.book = true` and
    `s.book.place.size = s.st.oracles.size` give the three facts. By `bookFacts_of_tests`
    (Johnson/Desc/K14/Law/BookFactsOfTests.lean) and `bookFitsB_iff`
    (Johnson/Desc/Sound/BookTestsLaw.lean).
  `hB_of_facts`: the premise hB, sign for sign, at any `get` and Rc under which these three hold.
  `hB_of_five`: the same where Rc gives a condition E on `get q`, and E with "no mark" gives the
    three and two facts more (X, Y: letters): the form in which a walk along the first chain's fold
    ends at "reached at the chain's end".
  `lastBookB`: the three as one test with code, for a file of evaluations. `book_of_lastBookB`: its
    accept gives the three facts. `hB_of_lastBookB`: hB where Rc gives its accept.

Limits. That any state has the three is not shown here. `lastBookB` asks more than the three facts
say (as many roots as trees; no place more than there are messages): so there is no converse.
Without the third premise the sentence is false by its form: the two tests read the book alone.
Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K14.Law.BookFactsOfTests
import Johnson.Desc.Sound.BookTestsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Book
open OnBytes
open VerifiableInference.Desc.Sound (NumberedBook bookFitsB bookFitsB_iff)
open VerifiableInference.Desc.K12.Door (atFirstBook)

/-- **The three facts on the book, from two tests and the equal counts.** -/
theorem book_of_three (s : First.S) (h1 : atFirstBook 0 s = true)
    (h2 : bookFitsB s.book = true) (h3 : s.book.place.size = s.st.oracles.size) :
    NumberedBook 0 s.book ∧ BookFits s.book ∧
      ∀ o, o < s.st.oracles.size → ∃ r : Nat × Nat, s.book.place[o]? = some r := by
  obtain ⟨a, b⟩ := VerifiableInference.Desc.K14.Law.bookFacts_of_tests s h1 h2 h3
  refine ⟨fun j t ht => ?_, (bookFitsB_iff s.book).1 h2, fun o ho => ?_⟩
  · rw [a j t ht, Nat.zero_add]
  · obtain ⟨q, hq, -⟩ := b o ho
    exact ⟨q, hq⟩

/-- **The premise hB of the law of the last table's row 0, sign for sign.** -/
theorem hB_of_facts {P S₁ P₀ : Type} (get : P × S₁ → P₀ × First.S) (Rc : P × S₁ → Prop)
    (h : ∀ q, Rc q → (get q).2.failed = none →
      atFirstBook 0 (get q).2 = true ∧ bookFitsB (get q).2.book = true ∧
        (get q).2.book.place.size = (get q).2.st.oracles.size) :
    ∀ q, Rc q → (get q).2.failed = none →
      NumberedBook 0 (get q).2.book ∧ BookFits (get q).2.book ∧
        ∀ o, o < (get q).2.st.oracles.size → ∃ r : Nat × Nat, (get q).2.book.place[o]? = some r :=
  fun q hq hm => book_of_three _ (h q hq hm).1 (h q hq hm).2.1 (h q hq hm).2.2

/-- **The same from a walk's end**: Rc gives E at `get q`; E and "no mark" give the three, and two
facts more. -/
theorem hB_of_five {P S₁ P₀ : Type} (get : P × S₁ → P₀ × First.S) (Rc : P × S₁ → Prop)
    (E : P₀ × First.S → Prop) (hE : ∀ q, Rc q → E (get q)) {X Y : P₀ × First.S → Prop}
    (H5 : ∀ p : P₀ × First.S, E p → p.2.failed = none →
      atFirstBook 0 p.2 = true ∧ bookFitsB p.2.book = true ∧
        p.2.book.place.size = p.2.st.oracles.size ∧ X p ∧ Y p) :
    ∀ q, Rc q → (get q).2.failed = none →
      NumberedBook 0 (get q).2.book ∧ BookFits (get q).2.book ∧
        ∀ o, o < (get q).2.st.oracles.size → ∃ r : Nat × Nat, (get q).2.book.place[o]? = some r :=
  hB_of_facts get Rc fun q hq hm =>
    ⟨(H5 _ (hE q hq) hm).1, (H5 _ (hE q hq) hm).2.1, (H5 _ (hE q hq) hm).2.2.1⟩

/-- The three as one test with code. -/
def lastBookB (s : First.S) : Bool :=
  atFirstBook 0 s && bookFitsB s.book && decide (s.book.place.size = s.st.oracles.size)

/-- Its accept gives the three facts. -/
theorem book_of_lastBookB (s : First.S) (h : lastBookB s = true) :
    NumberedBook 0 s.book ∧ BookFits s.book ∧
      ∀ o, o < s.st.oracles.size → ∃ r : Nat × Nat, s.book.place[o]? = some r := by
  unfold lastBookB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact book_of_three s h.1.1 h.1.2 h.2

/-- hB where Rc gives the test's accept. -/
theorem hB_of_lastBookB {P S₁ P₀ : Type} (get : P × S₁ → P₀ × First.S) (Rc : P × S₁ → Prop)
    (h : ∀ q, Rc q → (get q).2.failed = none → lastBookB (get q).2 = true) :
    ∀ q, Rc q → (get q).2.failed = none →
      NumberedBook 0 (get q).2.book ∧ BookFits (get q).2.book ∧
        ∀ o, o < (get q).2.st.oracles.size → ∃ r : Nat × Nat, (get q).2.book.place[o]? = some r :=
  fun q hq hm => book_of_lastBookB _ (h q hq hm)

end VerifiableInference.Desc.Book
