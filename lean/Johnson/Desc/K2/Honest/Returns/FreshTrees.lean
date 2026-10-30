-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/FreshTrees.lean: A TREE THAT A RECEIVING LAYS INTO THE BOOK HAS BEEN
OPENED AT NO LIST: its field `lists` is 0. On the ground's text alone (`recvP`,
Johnson/Desc/First/Base/Ground.lean): no state of the walk, no plan. The library's law on where a
receiving seats the new messages (`recvP_seat`, with `Seated`) says of a new tree its shape, number,
source and parts, nothing of that field. A tool for `AllOpen`'s clause "a tree of one list has not
been opened" (Returns/ReadOpen.lean). Statements with their proofs.

  `sentTrees_lists` a tree that `treesSent` (OnBytes/Slice/BlkSendRun.lean) appends has `lists` = 0.
                    THE LIBRARY's `sentTrees_made`: its lines stand here again at this field
  `entered_lists` the loop that enters the parts leaves every tree's `lists`. THE LIBRARY's
                    `entered_keeps`: its lines stand here again at this field
  `recvP_fresh` THE TOP: `recvP ft d sent = some (ids, d')` · a tree of d's later book at a number
                    from d's book's number of trees on ⊢ its `lists` is 0

By, all the library's: `sentTrees_old`, `recvP_seat` (Johnson/Desc/Book/BookFitsGround.lean) ·
`enterStep`, `enterStep_eq`, `enterStep_ne` (Johnson/Desc/Book/BookFits.lean) · `Seated`
(Johnson/Desc/Book/Seated.lean): the number of trees · `treesMade_eq`
(Johnson/Desc/Own/TreesAgree.lean). `recvP_fresh`'s first lines are `recvP_seat`'s. NEAR RELATIVES,
NOT CALLED: `treesSent_at` (a new tree of `treesSent`, written out whole) and `partsLaid_keep`
(entering parts turns no tree's shape, number or count of lists)
(Johnson/Prover/Link/BookLaid.lean): `sentTrees_lists` follows from the first; `entered_lists` is
general in the step and does not follow from the second, but it is spent here at `partsLaid`'s step
alone, where the second says more; `bookSentP_old` (Johnson/Prover/Link/ReadPay.lean): an old tree
stands whole behind a sending. That folder stands in the younger of the two sealed libraries over
which this file is compiled, not in the elder: so they are not called. None of them speaks of
`recvP`.

Limits. Nothing on adopting. Nothing on the field `oneList`. Nothing on any property.



-/
import Johnson.Desc.Book.BookFitsGround

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Book

variable {L : Type}

/-- A tree that `treesSent` appends has been opened at no list. -/
theorem sentTrees_lists (first : Nat) : ∀ (l : List TreeShape) (r : Nat) (A : Array Tree) (τ : Nat)
    (s' : TreeShape), l[τ]? = some s' →
    ∃ t : Tree, (treesSent first l r A)[A.size + τ]? = some t ∧ t.lists = 0
  | [], _, _, _, _, h => by cases h
  | s :: l, r, A, 0, s', _ => by
    refine ⟨{ shape := s, number := first + r, src := .own r }, ?_, rfl⟩
    show (treesSent first l (r + 1) (A.push _))[A.size + 0]? = _
    rw [sentTrees_old first l _ _ _ (by rw [Array.size_push]; omega), Array.getElem?_push,
      if_pos (Nat.add_zero _)]
  | s :: l, r, A, τ + 1, s', h => by
    obtain ⟨t, a, b⟩ := sentTrees_lists first l (r + 1)
      (A.push { shape := s, number := first + r, src := .own r }) τ s' h
    refine ⟨t, ?_, b⟩
    rw [Array.size_push, show A.size + 1 + τ = A.size + (τ + 1) by omega] at a
    exact a

/-- The loop that enters the parts leaves each tree's count of lists. -/
theorem entered_lists (tree : Array Nat) (base : Nat) (step : Tree → Nat → Tree)
    (hk : ∀ x i, (step x i).lists = x.lists) (T1 : Array Tree) :
    ∀ (k j : Nat) (t1 : Tree), T1[j]? = some t1 →
      ∃ t2 : Tree, ((List.range k).foldl (enterStep tree base step) T1)[j]? = some t2 ∧
        t2.lists = t1.lists := by
  intro k
  induction k with
  | zero => exact fun j t1 h => ⟨t1, h, rfl⟩
  | succ k ih =>
    intro j t1 h
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨t2, a, s1⟩ := ih j t1 h
    by_cases e : base + tree.getD k 0 = j
    · subst e
      exact ⟨step t2 k, enterStep_eq _ _ _ _ _ _ a, (hk t2 k).trans s1⟩
    · rw [enterStep_ne _ _ _ _ _ _ e]
      exact ⟨t2, a, s1⟩

/-- **A tree that a receiving lays has been opened at no list.** -/
theorem recvP_fresh (firstTree : Nat) (d d' : DState L) (sent : Array OracleNotice)
    (ids : Array Nat) (h : recvP firstTree d sent = some (ids, d')) {j : Nat} {t : Tree}
    (hj : d.book.trees.size ≤ j) (ht : d'.book.trees[j]? = some t) : t.lists = 0 := by
  obtain ⟨-, lay0, hl0, Se⟩ := recvP_seat firstTree d d' sent ids h
  unfold recvP at h
  rw [Own.treesMade_eq] at h
  split at h
  · cases hl : layTrees d.st.codes sent with
    | none => simp [hl] at h
    | some lay =>
      obtain rfl : lay0 = lay := Option.some.inj (hl0.symm.trans hl)
      simp only [hl, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      have hlt : j < d.book.trees.size + lay0.shapes.size := by
        have := (Array.getElem?_eq_some_iff.1 ht).1
        rw [Se.size] at this
        exact this
      obtain ⟨τ, rfl⟩ : ∃ τ, j = d.book.trees.size + τ := ⟨j - d.book.trees.size, by omega⟩
      have hτ : τ < lay0.shapes.size := by omega
      obtain ⟨t1, a1, z1⟩ := sentTrees_lists firstTree lay0.shapes.toList d.roots d.book.trees τ
        lay0.shapes[τ] (by rw [Array.getElem?_toList, Array.getElem?_eq_getElem hτ])
      obtain ⟨t2, a2, z2⟩ := entered_lists lay0.tree d.book.trees.size (fun x i => { x with
          parts := x.parts.push (d.st.oracles.size + i)
          oneList := x.oneList || (sent.getD i default).shape.answers == 0 }) (fun _ _ => rfl)
        _ sent.size _ t1 a1
      have e : some t = some t2 := ht.symm.trans a2
      rw [Option.some.inj e, z2, z1]
  · cases h

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.sentTrees_lists
#print axioms VerifiableInference.Desc.K2.Honest.Returns.entered_lists
#print axioms VerifiableInference.Desc.K2.Honest.Returns.recvP_fresh
