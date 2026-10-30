-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/ReadOpen.lean: THE TREES ARE OPENED ONE AFTER THE OTHER (`openOne`,
Johnson/Top/H0/Tw/K2/Switch.lean): THE LOOP RETURNS wherever premises on the make of the book and of
the handed columns hold; and what it returns is a term. Statements and proofs, over the library's
`openOne_iff` (Johnson/Top/H0/Tw/K2C/Asks.lean).

  `Taken`           an opened tree: its place in the book, its list, its columns
  `ownAt`           the list at which a tree of the book is opened under the positions
  `bookAfter`, `leftAfter`, `takenAfter`   what the loop leaves: the book (each opened tree counts
                    one list more); the columns not taken; for each tree its place, its list, its
                    columns
  `AllOpen`         the premises, tree by tree, at the columns that are left when its turn comes:
                    the tree is in the book · its sampled parts belong to the same groups, and to
                    one group at most where it holds a message without a sample (`leafOk`) · such a
                    tree has not been opened before · it is not longer than the positions' range ·
                    the next columns are as many as its list, each with its key, at the list's
                    position, of its width
  `open_returns`    the loop returns these three
  `ownAt_eq`        the program's list of a tree that is in the book
  `taken_find`      a tree of the list is found among what was taken, with its list and as many
                    columns

Limits. The trees of the list are different from each other: a premise. Nothing on any property.

-/
import Johnson.Top.H0.Tw.K2C.Asks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open _root_.Tw.K2 (Col openOne openOne_iff leafOk)

/-- An opened tree: its place in the book, the list at which it was opened, the columns there. -/
abbrev Taken : Type := Nat × Array Nat × Array (Array F)

/-- The list at which the tree at place t is opened; empty where the book has no such tree. -/
def ownAt (pos : Positions) (B0 : TreeBook) (t : Nat) : Array Nat :=
  ((B0.trees[t]?).map (Blk.ownList · pos)).getD #[]

/-- The book behind the loop. -/
def bookAfter : List Nat → TreeBook → TreeBook
  | [], B => B
  | t :: ts, B =>
    bookAfter ts { B with trees := B.trees.modify t fun x => { x with lists := x.lists + 1 } }

/-- The columns that the loop does not take. -/
def leftAfter (pos : Positions) (B0 : TreeBook) : List Nat → List OpenedColumn → List OpenedColumn
  | [], c => c
  | t :: ts, c => leftAfter pos B0 ts (c.drop (ownAt pos B0 t).size)

/-- What the loop takes, tree by tree. -/
def takenAfter (pos : Positions) (B0 : TreeBook) : List Nat → List OpenedColumn → List Taken
  | [], _ => []
  | t :: ts, c =>
    (t, ownAt pos B0 t, ((c.take (ownAt pos B0 t).size).map fun y => y.2.2.toArray).toArray) ::
      takenAfter pos B0 ts (c.drop (ownAt pos B0 t).size)

/-- **The premises, tree by tree.** c: the columns that are left when the first tree's turn comes.
-/
def AllOpen (S : Statement) (firstTree : Nat) (pos : Positions) (B0 : TreeBook) :
    List Nat → List OpenedColumn → Prop
  | [], _ => True
  | t :: ts, c => ∃ tree, B0.trees[t]? = some tree ∧ leafOk S tree = true ∧
      (tree.oneList = true → tree.lists = 0) ∧ tree.shape.logN ≤ pos.logN ∧
      (ownAt pos B0 t).size ≤ c.length ∧
      VerifiableInference.Desc.Own.colsStand (tree.number - firstTree)
        (tree.shape.mainWidth + tree.shape.maskWidth) (c.take (ownAt pos B0 t).size)
        (ownAt pos B0 t).toList = true ∧
      AllOpen S firstTree pos B0 ts (c.drop (ownAt pos B0 t).size)

theorem ownAt_eq {pos : Positions} {B0 : TreeBook} {t : Nat} {tree : Tree}
    (h : B0.trees[t]? = some tree) : Blk.ownList tree pos = ownAt pos B0 t := by
  unfold ownAt
  rw [h]
  rfl

/-- **The loop returns.** -/
theorem open_returns (S : Statement) (firstTree : Nat) (pos : Positions) (B0 : TreeBook) :
    ∀ (ts : List Nat) (B : TreeBook) (c : List OpenedColumn) (acc : Array Taken), ts.Nodup →
      (∀ t ∈ ts, B.trees[t]? = B0.trees[t]?) → AllOpen S firstTree pos B0 ts c →
      ts.foldlM (fun s t => openOne S firstTree pos B0 t s) (B, c, acc) =
        .ok (bookAfter ts B, leftAfter pos B0 ts c, acc ++ (takenAfter pos B0 ts c).toArray)
  | [], B, c, acc, _, _, _ => by
    show Except.ok (B, c, acc) = Except.ok (B, c, acc ++ (#[] : Array Taken))
    rw [Array.append_empty]
  | t :: ts, B, c, acc, hn, hB, hA => by
    obtain ⟨tree, h0, hl, ho, hr, he, hs, hrest⟩ := hA
    have e := ownAt_eq (pos := pos) h0
    have step : openOne S firstTree pos B0 t (B, c, acc) = .ok
        ({ B with trees := B.trees.modify t fun x => { x with lists := x.lists + 1 } },
          c.drop (ownAt pos B0 t).size,
          acc.push (t, ownAt pos B0 t,
            ((c.take (ownAt pos B0 t).size).map fun y => y.2.2.toArray).toArray)) :=
      (openOne_iff S firstTree pos B0 t _ _).2 ⟨tree, tree,
        { here := (hB t List.mem_cons_self).trans h0, there := h0, leaf := hl, once := ho
          range := hr
          count := by
            rw [e]
            exact (List.length_take ..).trans (Nat.min_eq_left he)
          stand := by
            rw [e]
            exact hs
          out := by rw [e] }⟩
    have ih := open_returns S firstTree pos B0 ts
      { B with trees := B.trees.modify t fun x => { x with lists := x.lists + 1 } }
      (c.drop (ownAt pos B0 t).size)
      (acc.push (t, ownAt pos B0 t,
        ((c.take (ownAt pos B0 t).size).map fun y => y.2.2.toArray).toArray))
      (List.nodup_cons.1 hn).2
      (fun t' ht' => by
        have hne : t ≠ t' := fun h => (List.nodup_cons.1 hn).1 (h ▸ ht')
        show (B.trees.modify t _)[t']? = _
        rw [Array.getElem?_modify, if_neg hne]
        exact hB t' (List.mem_cons_of_mem _ ht'))
      hrest
    rw [List.foldlM_cons, step]
    refine ih.trans ?_
    show Except.ok (_, _, _) = Except.ok (_, _, _)
    have ea : ∀ (x : Taken) (l : List Taken),
        acc.push x ++ l.toArray = acc ++ (x :: l).toArray := by
      intro x l
      apply Array.toList_inj.1
      simp
    rw [ea]
    rfl

/-- A tree of the list is found among what was taken. -/
theorem taken_find (S : Statement) (firstTree : Nat) (pos : Positions) (B0 : TreeBook) :
    ∀ (ts : List Nat) (c : List OpenedColumn) (t : Nat), t ∈ ts → AllOpen S firstTree pos B0 ts c →
      ∃ cs, (takenAfter pos B0 ts c).find? (·.1 == t) = some (t, ownAt pos B0 t, cs) ∧
        cs.size = (ownAt pos B0 t).size
  | t' :: ts, c, t, hm, hA => by
    obtain ⟨_, _, _, _, _, he, _, hrest⟩ := hA
    by_cases h : t' = t
    · subst h
      refine ⟨_, List.find?_cons_of_pos (by simp), ?_⟩
      rw [List.size_toArray, List.length_map, List.length_take]
      exact Nat.min_eq_left he
    · have hm' : t ∈ ts := by
        rcases List.mem_cons.1 hm with h' | h'
        · exact absurd h'.symm h
        · exact h'
      obtain ⟨cs, f, z⟩ := taken_find S firstTree pos B0 ts _ t hm' hrest
      refine ⟨cs, ?_, z⟩
      show List.find? _ (_ :: _) = _
      rw [List.find?_cons_of_neg (by simpa using h)]
      exact f

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.open_returns
#print axioms VerifiableInference.Desc.K2.Honest.Returns.taken_find
