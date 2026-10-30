-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookFree.lean: WHAT THE BOOK's MAKER's TEST `wantsFree`
(Honest/BookEntries.lean) GIVES WHERE IT SAYS YES. Three statements with proofs, by unfolding; no
definition.

  `wantsFree_free`      every stretch lies within its message's free entries:
                       `w.number + w.count ≤ w.msg.free`
  `wantsFree_below`     so each of its numbers is below `w.msg.free`
  `wantsFree_apart`     two stretches of one message, at two places of the list, do not meet

THAT THE MAKER ASKS THE TEST, AND OF WHICH LIST, IS NOT SAID HERE: it is `spendingBook_open`
(Honest/BookRowStretch.lean): where `spendingBook` (Honest/BookAll.lean) returns a book, the test
says yes at the list that `linksWants` returns there with what `loneWants` lays behind it, both
written out in the statement, and the book's entries begin with that list's entries. So the maker
asks it of the segments' parts' stretches (of the segments' mask rows, and of the index-mask message
where a part's end values are laid under it) and of the lone sums' behind the segments; not of the
entries on fold masks, which are no stretches of this form, nor of the shared split's one coin,
which is made as such a stretch (`splitEntry`, Honest/BookAll.lean) and left out of the tested list.
An elder issue of this file had a lemma `spendingBook_free` for that: its list stood under "there
is" and was tied to the maker by nothing, so the empty list met it at every book: it said nothing,
and is struck.

Limits. Each lemma has the test's yes at the caller's own list as a hypothesis. `MsgAt.free` is a
field: at the owners that `ownerOf` (Honest/BookEntries.lean) makes it is the programs' own count
`Send.freeMaskEntries`, called there; these lemmas read the field alone. Nothing on a run, a coin's
value or a measure. This file proves nothing about soundness, completeness, hiding or any other
property of the protocol.

-/
import Johnson.Desc.ProofFile.Honest.BookEntries

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

theorem wantsFree_free {ws : List Want} (h : wantsFree ws = true) {w : Want} (hw : w ∈ ws) :
    w.number + w.count ≤ w.msg.free := by
  unfold wantsFree at h
  exact of_decide_eq_true (List.all_eq_true.1 (Bool.and_eq_true_iff.1 h).1 w hw)

theorem wantsFree_below {ws : List Want} (h : wantsFree ws = true) {w : Want} (hw : w ∈ ws)
    {j : Nat} (hj : j < w.count) : w.number + j < w.msg.free :=
  Nat.lt_of_lt_of_le (Nat.add_lt_add_left hj _) (wantsFree_free h hw)

theorem wantsFree_apart {ws : List Want} (h : wantsFree ws = true) {a b : Want × Nat}
    (ha : a ∈ ws.zipIdx) (hb : b ∈ ws.zipIdx) (hn : a.2 ≠ b.2) (hm : a.1.msg = b.1.msg) :
    meets a.1.number a.1.count b.1.number b.1.count = false := by
  unfold wantsFree at h
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 (Bool.and_eq_true_iff.1 h).2 a ha) b hb
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true'] at h1
  rcases h1 with (h2 | h2) | h2
  · exact absurd h2 hn
  · exact absurd hm h2
  · exact h2

end ProofFile.Honest

#print axioms ProofFile.Honest.wantsFree_free
#print axioms ProofFile.Honest.wantsFree_below
#print axioms ProofFile.Honest.wantsFree_apart
