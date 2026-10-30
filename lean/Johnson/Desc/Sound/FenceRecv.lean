-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FenceRecv.lean: THE FENCE's TERM (`bookSeat`, Johnson/Desc/Sound/Fence.lean) AT THE LIBRARY's OWN TEXT OF A RECEIVING:
what the book of trees is behind a prover's message with oracle messages (OnBytes/Slice/BlkSendRun.lean:
`treesSent`, `partsLaid`; the book of `bookSent`; by reading, also of the description's `recvD`,
Johnson/Desc/K1/Law/Writes3.lean, which is not in the build on which this file was written). One definition and six theorems on plain data:
no routine is run, no piece is named.

  `recvBook first bk sent lay n0 roots`: that book, written out with the library's two functions, at bare data (
    `bookSent` takes the program's whole context). `bookSent_eq`: it is `bookSent` at the context's data: rfl.
  `partsLaid_src`: entering parts into trees changes no tree's source (`partsLaid_public` has the like
    for shape and number: its proof, with src).
  `treesSent_new_src`: the τ-th of the appended trees has the source "own (roots + τ)".
  `bookSeat_old`: A MESSAGE THAT HAS A SEAT KEEPS IT. (Not: a message without a seat stays without: that is false: why
    `BookKept` is asked under the fence.) By `partsLaid_old`, `treesSent_old`.
  `bookSeat_new`: the i-th new message is seated at lo + (roots + lay.tree i), where the layout's tree number is one
    of its shapes'.
  `bookSeat_new_lt`: so below lo + (roots + the number of the layout's shapes): THE NEW COUNT.
FOR WHOEVER PAYS `BookKept` AT A SENDING, at K := `bookedOf lo low stOf bookOf rootsOf` (any low): "old"'s second half, and "new", are these,
once the record behind a yes is shown to hold this book, roots + lay.shapes.size roots, and the statement's
messages with sent.size more (`stSent_size`); with "the book has a place for each message and no other".
"more" then wants: the piece's stretch lists lay.shapes.size trees.
Nearest kin: `BookKeeps` (OnBytes/Slice/BlkSeat.lean: place, shape, NUMBER, parts are kept; `bookSent_keeps`) ·
`FitAt`, `fit_sent` (OnBytes/Tie/Pv/Keeps/FitBook.lean: a place names a tree that holds the message). Neither speaks of
the source, nor of a bound on the tree's number.

Every "there is", walked: none.
Limits. Plain data. It closes no row. Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.Fence
import OnBytes.Slice.BlkSentSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes
open OnBytes.Slice (treesSent partsLaid treesSent_old partsLaid_old)

/-- The book behind a prover's message with oracle messages. -/
def recvBook (first : ℕ) (bk : TreeBook) (sent : Array OracleNotice) (lay : TreeLay) (n0 roots : ℕ) :
    TreeBook :=
  { trees := partsLaid sent lay n0 bk.trees.size (treesSent first lay.shapes.toList roots bk.trees)
    place := bk.place ++ (Array.range sent.size).map fun i =>
      (bk.trees.size + lay.tree.getD i 0, lay.part.getD i 0) }

/-- The program's book behind such a message (`bookSent`) is that, at the context's own data. -/
theorem bookSent_eq (c : Ctx) (sent : Array OracleNotice) (lay : TreeLay) :
    OnBytes.Slice.bookSent c sent lay =
      recvBook c.ch.firstTree c.book sent lay c.st.oracles.size c.ch.roots := rfl

/-- Entering parts into trees changes no tree's source. -/
theorem partsLaid_src (sent : Array OracleNotice) (lay : TreeLay) (n0 base : ℕ) (trees : Array Tree)
    (t : ℕ) :
    ((partsLaid sent lay n0 base trees)[t]?).map (·.src) = (trees[t]?).map (·.src) := by
  unfold partsLaid
  generalize List.range sent.size = l
  induction l generalizing trees with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons, ih, Array.getElem?_modify]
    split
    · rw [Option.map_map]
      rfl
    · rfl

/-- The τ-th of the appended trees has the source "own (roots + τ)". -/
theorem treesSent_new_src (first : ℕ) : ∀ (l : List TreeShape) (r : ℕ) (A : Array Tree) (τ : ℕ),
    τ < l.length → ((treesSent first l r A)[A.size + τ]?).map (·.src) = some (.own (r + τ))
  | [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | s :: l, r, A, 0, _ => by
    show ((treesSent first l (r + 1) (A.push _))[A.size + 0]?).map (·.src) = _
    rw [treesSent_old first l _ _ _ (by rw [Array.size_push]; omega), Array.getElem?_push,
      if_pos (Nat.add_zero _)]
    rfl
  | s :: l, r, A, τ + 1, h => by
    have ih := treesSent_new_src first l (r + 1)
      (A.push { shape := s, number := first + r, src := .own r }) τ (Nat.lt_of_succ_lt_succ h)
    rw [Array.size_push] at ih
    have e1 : A.size + (τ + 1) = A.size + 1 + τ := by omega
    have e2 : r + (τ + 1) = r + 1 + τ := by omega
    show ((treesSent first l (r + 1) (A.push _))[A.size + (τ + 1)]?).map (·.src) = _
    rw [e1, e2]
    exact ih

/-- **A message that has a seat keeps it.** -/
theorem bookSeat_old (lo : ℕ) (low : Tree → Option ℕ) (first : ℕ) (bk : TreeBook)
    (sent : Array OracleNotice) (lay : TreeLay) (n0 roots o j : ℕ)
    (h : bookSeat lo low bk o = some j) :
    bookSeat lo low (recvBook first bk sent lay n0 roots) o = some j := by
  unfold bookSeat at h ⊢
  obtain ⟨pl, hpl, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.1 h
  have ho : o < bk.place.size := by
    rcases Nat.lt_or_ge o bk.place.size with h1 | h1
    · exact h1
    · rw [Array.getElem?_eq_none h1] at hpl
      cases hpl
  have htt : pl.1 < bk.trees.size := by
    rcases Nat.lt_or_ge pl.1 bk.trees.size with h1 | h1
    · exact h1
    · rw [Array.getElem?_eq_none h1] at ht
      cases ht
  have e1 : (recvBook first bk sent lay n0 roots).place[o]? = some pl := by
    show (bk.place ++ _)[o]? = some pl
    rw [Array.getElem?_append_left ho]
    exact hpl
  have e2 : (recvBook first bk sent lay n0 roots).trees[pl.1]? = some t := by
    show (partsLaid sent lay n0 bk.trees.size (treesSent first _ roots bk.trees))[pl.1]? = some t
    rw [partsLaid_old _ _ _ _ _ pl.1 htt, treesSent_old _ _ _ _ pl.1 htt]
    exact ht
  rw [e1, Option.bind_some, e2, Option.bind_some]
  exact h

/-- **Where a new message is seated.** -/
theorem bookSeat_new (lo : ℕ) (low : Tree → Option ℕ) (first : ℕ) (bk : TreeBook)
    (sent : Array OracleNotice) (lay : TreeLay) (n0 roots i : ℕ) (hi : i < sent.size)
    (hτ : lay.tree.getD i 0 < lay.shapes.size) :
    bookSeat lo low (recvBook first bk sent lay n0 roots) (bk.place.size + i) =
      some (lo + (roots + lay.tree.getD i 0)) := by
  have e1 : (recvBook first bk sent lay n0 roots).place[bk.place.size + i]? =
      some (bk.trees.size + lay.tree.getD i 0, lay.part.getD i 0) := by
    show (bk.place ++ _)[bk.place.size + i]? = _
    rw [Array.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      Array.getElem?_map, Array.getElem?_range, if_pos hi]
    rfl
  have e2 : ((recvBook first bk sent lay n0 roots).trees[bk.trees.size + lay.tree.getD i 0]?).map
      (·.src) = some (.own (roots + lay.tree.getD i 0)) :=
    (partsLaid_src sent lay n0 bk.trees.size (treesSent first lay.shapes.toList roots bk.trees)
      (bk.trees.size + lay.tree.getD i 0)).trans
      (treesSent_new_src first lay.shapes.toList roots bk.trees _
        (by rw [Array.length_toList]; exact hτ))
  obtain ⟨t, ht, hs⟩ := Option.map_eq_some_iff.1 e2
  unfold bookSeat
  rw [e1, Option.bind_some, ht, Option.bind_some]
  show (match t.src with
    | .own n => some (lo + n)
    | .given _ _ => low t) = _
  rw [hs]

/-- So it is seated below the new count. -/
theorem bookSeat_new_lt (lo : ℕ) (low : Tree → Option ℕ) (first : ℕ) (bk : TreeBook)
    (sent : Array OracleNotice) (lay : TreeLay) (n0 roots i : ℕ) (hi : i < sent.size)
    (hτ : lay.tree.getD i 0 < lay.shapes.size) :
    ∃ j, bookSeat lo low (recvBook first bk sent lay n0 roots) (bk.place.size + i) = some j ∧
      j < lo + (roots + lay.shapes.size) :=
  ⟨_, bookSeat_new lo low first bk sent lay n0 roots i hi hτ, by omega⟩

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.bookSent_eq
#print axioms VerifiableInference.Desc.Sound.bookSeat_old
#print axioms VerifiableInference.Desc.Sound.bookSeat_new
#print axioms VerifiableInference.Desc.Sound.bookSeat_new_lt
