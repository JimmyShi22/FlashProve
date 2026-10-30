-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/RowAtStep.lean: a step of kind K1, as the kind's own relations describe it,
leaves what the item "row" reads of the record (`RowKept`, Johnson/Desc/K1/Law/RowBack.lean): so the
item goes back over it.

The relations: `OldMsgs` (Johnson/Desc/K1/Law/GoodSend5.lean), `Booked`
(Johnson/Desc/K1/Law/BookAtRecord.lean), `TreesOlder` (Johnson/Desc/K1/Law/EarlierTreesUnchanged.lean), and
"every group in front stands behind with its open rows", which `Joins.rowsKept`
(Johnson/Desc/K1/Law/JoinsRows.lean) gives from `Joins`.

Main names: `rowKept_of_step`; `row_holds_back_of_step`.

What is not claimed. Three premises are on the record in front, and are shown of no record here: the
statement is in order; the book has a place for every message and no more; every place of the book
names a tree that the book holds. AT ONE WITNESS. Nothing on soundness, on an honest prover or on
hiding.

-/
import Johnson.Desc.K1.Law.RowBack
import Johnson.Desc.K1.Law.EarlierTreesUnchanged
import Johnson.Desc.K1.Law.GoodSend5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes.Means (InOrder)
open OnBytes.Maker Fo.Peel Cb Johnson.Pack
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (S Numbers RowClass Item Meaning rowSays wordsAtFirst)

/-- **A step of the kind leaves what the item "row" reads.** -/
theorem rowKept_of_step (P : Par) (s s' : S) (hO : OldMsgs s.st s'.st)
    (hR : ∀ (j : Nat) (G : OnBytes.Group), s.st.groups[j]? = some G →
      ∃ G' : OnBytes.Group, s'.st.groups[j]? = some G' ∧ G'.rows = G.rows)
    (hB : Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size)
    (hT : TreesOlder s.book s'.book) (hn : s.book.place.size = s.st.oracles.size)
    (hold : ∀ (o : Nat) (x : Nat × Nat), s.book.place[o]? = some x → x.1 < s.book.trees.size) :
    RowKept s s' where
  codes := hO.1
  msgs := hO.2
  rows := hR
  place := fun o ho => hB.older (by omega)
  trees := fun o q hq => hT q.1 (hold o q hq)

variable {Pp Cells Tok : Type}

/-- **So the item goes back over it**, for every meaning whose letter `row` is the ruled
sentence. -/
theorem row_holds_back_of_step (arr : ℕ → ℕ → ℕ) (N : Numbers)
    (Mg : Meaning Pp (Wit Cells Tok MsgT)) (hrow : Mg.row = rowSays N (wordsAtFirst arr))
    (P : Par) (x x' : Pp × S) (y y' : Strs) (w : Wit Cells Tok MsgT)
    (m : Nat) (c : RowClass) (hO : OldMsgs x.2.st x'.2.st)
    (hR : ∀ (j : Nat) (G : OnBytes.Group), x.2.st.groups[j]? = some G →
      ∃ G' : OnBytes.Group, x'.2.st.groups[j]? = some G' ∧ G'.rows = G.rows)
    (hB : Booked P x.2.book x.2.st.oracles.size x'.2.book x'.2.st.oracles.size)
    (hT : TreesOlder x.2.book x'.2.book) (hI : InOrder x.2.st)
    (hn : x.2.book.place.size = x.2.st.oracles.size)
    (hold : ∀ (o : Nat) (q : Nat × Nat), x.2.book.place[o]? = some q →
      q.1 < x.2.book.trees.size)
    (h : (Item.row m c).holds N Mg x' y' w) : (Item.row m c).holds N Mg x y w :=
  row_holds_back arr N Mg hrow m c x x' y y' w hI
    (rowKept_of_step P x.2 x'.2 hO hR hB hT hn hold) h

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.rowKept_of_step
#print axioms VerifiableInference.Desc.K1.row_holds_back_of_step
