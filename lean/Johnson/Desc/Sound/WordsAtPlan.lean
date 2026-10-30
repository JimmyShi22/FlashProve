-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/WordsAtPlan.lean: THE FIRST CHAIN's READER OF A ROW's WORDS, `wordsFirst`
(Johnson/Desc/Sound/WordsAt.lean), AT THE PLAN's OWN SHAPES AND THE BOOK's OWN PLACES. Theorems with
their proofs.

WHY. The reader of a row's words in the layer
for the table's item "row" is `wordsFirst arr s.st s.book w`; it has three seams,
each with the public test of the promise that closes it:
  (1) it takes a message's SHAPE from the record (`S.oracles[o].shape`), while the pins take it from
      the plan's member at that seat;
  (2) `noFirst` reads a tree's number off the tree, not its place in the book;
  (3) where the message o has no seat, or the statement no such message, it reads the zero table, in
      silence.
Here each seam is closed under its test's plain sentence, as a premise.

  THE THREE SENTENCES, WRITTEN OUT AS PREMISES (no name is coined for them: the tests have their
    own: "K12.msgShapes" · "K12.bookInOrder" · the promise's `bookAt` with "K12.seatsCarried"):
    h₁: below the number of the statement's messages, the shape of message o is M[o] (M: the plan's
    sendings' shapes, in order) · h₂: the tree at the place z of the book bears the number z · h₃:
    every message of the statement has a place in the book, at a tree that is there.
  `seatFirst_atPlan`: under h₂ and h₃ the seat of a message is its place in the book.
  **`tabFirst_at_plan`**: under all three, for o below the number of the statement's messages: M has
    a shape sh at o, the book a place q, and the table that `wordsFirst` reads at o is the witness's
    one accessor `Wit.tab` at sh and q: NO ZERO TABLE, NO SHAPE OFF THE RECORD, NO NUMBER OFF THE
    TREE.

Limits. Book-keeping: nothing on soundness. The three sentences are premises: that the promise's
public tests give them is their layers' lemmas. General in M: that M is the plan's is not said here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.WordsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes (Statement TreeBook Tree OracleShape)
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice

/-- Under (2) and (3): the seat of a message is its place in the book. -/
theorem seatFirst_atPlan (st : Statement) (B : TreeBook)
    (h₂ : ∀ (z : ℕ) (T : Tree), B.trees[z]? = some T → T.number = z)
    (h₃ : ∀ o, o < st.oracles.size → ∃ q : ℕ × ℕ, B.place[o]? = some q ∧ q.1 < B.trees.size)
    (o : ℕ) (ho : o < st.oracles.size) :
    ∃ q, B.place[o]? = some q ∧ seatBy noFirst B o = some q := by
  obtain ⟨q, hq, hz⟩ := h₃ o ho
  have hT : B.trees[q.1]? = some B.trees[q.1] := Array.getElem?_eq_getElem hz
  refine ⟨q, hq, ?_⟩
  rw [seatBy_some noFirst B o q _ hq hT]
  show some ((B.trees[q.1]).number, q.2) = some q
  rw [h₂ q.1 _ hT]

section
variable {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)

/-- **The table that `wordsFirst` reads at a message of the statement.** -/
theorem tabFirst_at_plan (M : List OracleShape) (st : Statement) (B : TreeBook)
    (h₁ : ∀ o, o < st.oracles.size → (st.oracles[o]?).map (·.shape) = M[o]?)
    (h₂ : ∀ (z : ℕ) (T : Tree), B.trees[z]? = some T → T.number = z)
    (h₃ : ∀ o, o < st.oracles.size → ∃ q : ℕ × ℕ, B.place[o]? = some q ∧ q.1 < B.trees.size)
    (w : Wit Cells Tok MsgT) (o : ℕ) (ho : o < st.oracles.size) :
    ∃ sh q, M[o]? = some sh ∧ B.place[o]? = some q ∧
      tabAt st.codes arr (seatBy noFirst B) st w o = w.tab st.codes sh (arr q.1 q.2) q.1 q.2 := by
  obtain ⟨q, hq, hs⟩ := seatFirst_atPlan st B h₂ h₃ o ho
  have hx : st.oracles[o]? = some st.oracles[o] := Array.getElem?_eq_getElem ho
  have hm := h₁ o ho
  rw [hx, Option.map_some] at hm
  refine ⟨_, q, hm.symm, hq, ?_⟩
  unfold tabAt
  rw [hs, hx]

/-- So `wordsFirst` is `wordsOn` at a table that, below the number of the statement's messages, is
that accessor. -/
theorem wordsFirst_is (st : Statement) (B : TreeBook) (w : Wit Cells Tok MsgT) :
    wordsFirst arr st B w =
      OnBytes.Means.wordsOn st (tabAt st.codes arr (seatBy noFirst B) st w) := rfl

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.seatFirst_atPlan
#print axioms VerifiableInference.Desc.Sound.tabFirst_at_plan
#print axioms VerifiableInference.Desc.Sound.wordsFirst_is
