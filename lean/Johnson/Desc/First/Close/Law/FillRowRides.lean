-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/FillRowRides.lean: THE ITEM "row" RIDES, BACKWARDS, AT THE RULED
READER, UNDER PREMISES ON THE TWO STATES ALONE. Statements and proofs. A file BESIDE the table of
joints.

Why. `rowSays_back` (FillRow.lean, beside this file) asks that the reader gives the same words at
the messages of the statement in front. The ruled reader `wordsFirst`
(Johnson/Desc/Sound/WordsAt.lean) reads, of the state, the statement (its table of codes; a
message's shape) and the book (a message's place; the tree there). That file's own lemma of this
sort, `words_older`, speaks of the LAST chain's reader; for the first chain's there is none. Its two
general tools give it.
  `wordsFirst_older`: at a message o: one table of codes, o's shape the same, o's place in the book
    the same, the tree at that place the same: the same words at o. By `wordsBy_congr` and
    `seatBy_frame`.
  `BookKept s s'`: every message of the statement in front keeps its place in the book, and the tree
    there.
  `rowSaysFirst_back`: so `rowSays N (wordsAtFirst arr) m c` rides backwards from b to a, AT ONE
    WITNESS, under: the statement in front is in order; the statement behind extends it; the class's
    rows in front are still among those behind; `BookKept a.2 b.2`.
Limits. AT ONE WITNESS w: at a block whose extractor lays something (K1's, K2's, K10's, K12's rows
of the table) the witness in front is another than the witness behind: there the words agree only if
what is laid lies at other seats than the riding class's messages': not treated. `BookKept` is a
premise: shown of no block. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.FillRowFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

open OnBytes (Statement TreeBook)
open OnBytes.Means (Words InOrder Extends)
open OnBytes.Slice (GE)
open OnBytes.Maker Fo.Peel Cb Johnson.Pack
open VerifiableInference.Desc.Sound (wordsFirst wordsBy_congr seatBy_frame noFirst MsgT)

variable {P Cells Tok : Type}

/-- **The first chain's reader gives a message the same words at a later statement and book** that
keep the table of codes, the message's shape, its place and the tree there. -/
theorem wordsFirst_older (arr : ℕ → ℕ → ℕ) (st st' : Statement) (B B' : TreeBook)
    (w : Wit Cells Tok MsgT) (o : ℕ) (hc : st'.codes = st.codes)
    (hx : (st'.oracles[o]?).map (·.shape) = (st.oracles[o]?).map (·.shape))
    (hp : B'.place[o]? = B.place[o]?)
    (ht : ∀ q, B.place[o]? = some q → B'.trees[q.1]? = B.trees[q.1]?) (part : OnBytes.Part)
    (i : ℕ) :
    wordsFirst arr st' B' w o part i = wordsFirst arr st B w o part i :=
  wordsBy_congr arr _ _ st st' w o o hc (seatBy_frame noFirst B B' o hp ht) hx part i

/-- Every message of the statement in front keeps its place in the book, and the tree there. -/
def BookKept (s s' : S) : Prop :=
  ∀ o, o < s.st.oracles.size → s'.book.place[o]? = s.book.place[o]? ∧
    ∀ q, s.book.place[o]? = some q → s'.book.trees[q.1]? = s.book.trees[q.1]?

/-- **The item "row" rides, backwards, at the ruled reader.** -/
theorem rowSaysFirst_back (arr : ℕ → ℕ → ℕ) (N : Numbers) (m : Nat) (c : RowClass) (a b : P × S)
    (y y' : Strs) (w : Wit Cells Tok MsgT) (hI : InOrder a.2.st) (hE : Extends a.2.st b.2.st)
    (hsub : ∀ r ∈ classRows N m c a.2, r ∈ classRows N m c b.2) (hB : BookKept a.2 b.2)
    (h : rowSays N (wordsAtFirst arr) m c b y' w) : rowSays N (wordsAtFirst arr) m c a y w := by
  refine rowSays_back N (wordsAtFirst arr) m c a b y y' w w hI hE hsub (fun o ho part i _ => ?_) h
  obtain ⟨x', hx', e⟩ := hE.shape o _ (Array.getElem?_eq_getElem ho)
  refine wordsFirst_older arr a.2.st b.2.st a.2.book b.2.book w o hE.codes ?_ (hB o ho).1
    (hB o ho).2 part i
  rw [hx', Array.getElem?_eq_getElem ho, Option.map_some, Option.map_some, e]

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.wordsFirst_older
#print axioms VerifiableInference.Desc.First.rowSaysFirst_back
