-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkSentSeat.lean: where the oracle messages of a prover's message are in the book of
trees.

When the prover sends oracle messages, the program enters them into the statement and their trees
into the book (OnBytes/Slice/BlkSendRun.lean: `stSent`, `bookSent`). A later block reads them by the
book. This file shows two things, for every such message.
 What is older stays: no older tree and no older place changes (`bookSent_keeps`).
 Where the new ones are (`seat_of_sent`): if the program has put all of them in one tree, part
   number i for the i-th of them, they are the parts of that tree in the order of sending
   (OnBytes/Slice/BlkSeat.lean: `Seat`), and the tree has the next number of the chain.

Main theorems: `treesSent_old`, `partsLaid_old`, `bookSent_keeps`, `partsLaid_public`,
`admitted_shape`, `joined_shape`, `shapesKeep_of_map`, `seat_of_sent`.
Not claimed. How the program puts oracle messages in trees: that all are in one tree, and what the
tree's shape lists, are hypotheses of `seat_of_sent`. So is that, before the message, the book has a
place for each oracle message of the statement and for no other. Nothing on soundness.
-/
import OnBytes.Slice.BlkStLaws
import OnBytes.Slice.BlkSeat

set_option autoImplicit false

namespace OnBytes.Slice

/-! ## A prover's message with oracle messages changes nothing older in the book -/

/-- Trees that are appended to the others leave the others as they were. -/
theorem treesSent_old (first : Nat) : ∀ (l : List TreeShape) (roots : Nat) (trees : Array Tree)
    (t : Nat), t < trees.size → (treesSent first l roots trees)[t]? = trees[t]?
  | [], _, _, _, _ => rfl
  | s :: l, roots, trees, t, h => by
    show (treesSent first l (roots + 1) (trees.push _))[t]? = _
    rw [treesSent_old first l (roots + 1) _ t (by rw [Array.size_push]; omega),
      Array.getElem?_push_lt h, Array.getElem?_eq_getElem h]

/-- Parts that are entered into trees from the number base on leave the trees before it as they
were. -/
theorem partsLaid_old (sent : Array OracleNotice) (lay : TreeLay) (n0 base : Nat)
    (trees : Array Tree) (t : Nat) (h : t < base) :
    (partsLaid sent lay n0 base trees)[t]? = trees[t]? := by
  unfold partsLaid
  generalize List.range sent.size = l
  induction l generalizing trees with
  | nil => rfl
  | cons i l ih =>
    rw [List.foldl_cons, ih, Array.getElem?_modify, if_neg (by omega)]

/-- The book after a prover's message with oracle messages keeps what the book before it
said. -/
theorem bookSent_keeps (c : Ctx) (sent : Array OracleNotice) (lay : TreeLay) :
    BookKeeps c.book (bookSent c sent lay) := by
  constructor
  · intro o p h
    have ho : o < c.book.place.size := by
      rcases Nat.lt_or_ge o c.book.place.size with h1 | h1
      · exact h1
      · rw [Array.getElem?_eq_none h1] at h
        cases h
    show (c.book.place ++ _)[o]? = some p
    rw [Array.getElem?_append_left ho]
    exact h
  · intro t T h
    have ht : t < c.book.trees.size := by
      rcases Nat.lt_or_ge t c.book.trees.size with h1 | h1
      · exact h1
      · rw [Array.getElem?_eq_none h1] at h
        cases h
    refine ⟨T, ?_, rfl, rfl, rfl⟩
    show (partsLaid sent lay _ c.book.trees.size (treesSent _ _ _ c.book.trees))[t]? = some T
    rw [partsLaid_old _ _ _ _ _ t ht, treesSent_old _ _ _ _ t ht]
    exact h

/-! ## Shapes -/

/-- Entering the sample rows of an oracle message changes no shape. -/
theorem admitted_shape (S : Statement) (o : Nat) (s : OracleShape) (places : List PadPlace)
    (rows : Array Row) (i : Nat) :
    ((admitted S o s places rows).oracles[i]?).map (·.shape) = (S.oracles[i]?).map (·.shape) := by
  unfold admitted
  simp only [Array.getElem?_modify]
  split
  · rw [Option.map_map]
    rfl
  · rfl

/-- Joining a group changes no shape. -/
theorem joined_shape (S : Statement) (g o : Nat) (kept : Bool) (G : Group) (i : Nat) :
    ((withMessageInGroup S g o kept G).oracles[i]?).map (·.shape) = (S.oracles[i]?).map (·.shape) := by
  unfold withMessageInGroup
  simp only [Array.getElem?_modify]
  split
  · rw [Option.map_map]
    rfl
  · rfl

/-- Entering parts into trees changes no tree's shape and number. -/
theorem partsLaid_public (sent : Array OracleNotice) (lay : TreeLay) (n0 base : Nat)
    (trees : Array Tree) (t : Nat) :
    ((partsLaid sent lay n0 base trees)[t]?).map (fun x => (x.shape, x.number))
      = (trees[t]?).map fun x => (x.shape, x.number) := by
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

/-- A statement that has the same shape at every number keeps each oracle message's shape. -/
theorem shapesKeep_of_map (S S' : Statement)
    (h : ∀ i : Nat, (S'.oracles[i]?).map (·.shape) = (S.oracles[i]?).map (·.shape)) :
    ShapesKeep S S' := by
  intro o x hx
  have h1 := h o
  rw [hx] at h1
  cases hx' : S'.oracles[o]? with
  | none => rw [hx'] at h1; cases h1
  | some x' => rw [hx'] at h1; exact ⟨x', rfl, Option.some.inj h1⟩

/-! ## The new tree -/

/-- The oracle messages of one prover's message that the program has put in one tree are the
parts of that tree, in the order of sending. c: the context before the message. cB: a context
whose book is the book after the message and whose statement has the shapes of the statement after
it. sh: the tree's shape. Asked besides: the shape lists the messages' symbols (`hmain`, `hmask`),
and before the message the book has as many places as the statement has oracle messages (`hp`). -/
theorem seat_of_sent (c cB : Ctx) (sent : Array OracleNotice) (lay : TreeLay) (sh : TreeShape)
    (hp : c.st.oracles.size = c.book.place.size) (hb : cB.book = bookSent c sent lay)
    (hs : ∀ i : Nat, (cB.st.oracles[i]?).map (·.shape)
      = ((stSent c.st sent).oracles[i]?).map (·.shape))
    (h1 : lay.shapes = #[sh])
    (ht : ∀ i, i < sent.size → lay.tree.getD i 0 = 0 ∧ lay.part.getD i 0 = i)
    (hmain : sh.mainSymbols
      = ((sent.toList.map (·.shape)).map fun s => s.mainRows * s.mainDeg).toArray)
    (hmask : sh.maskSymbols
      = ((sent.toList.map (·.shape)).map fun s => s.maskRows * 3).toArray) :
    Seat cB ((List.range sent.size).map (· + c.st.oracles.size))
      (c.ch.firstTree + c.ch.roots) sh.logN (sent.toList.map (·.shape)) := by
  have hid : ∀ w, w < sent.size →
      ((List.range sent.size).map (· + c.st.oracles.size)).getD w 0
        = w + c.st.oracles.size := by
    intro w hw
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hw]
    rfl
  refine ⟨by simp, ?_, ?_⟩
  · -- the tree
    have hpub := partsLaid_public sent lay c.st.oracles.size c.book.trees.size
      (treesSent c.ch.firstTree lay.shapes.toList c.ch.roots c.book.trees) c.book.trees.size
    rw [h1] at hpub
    have hnew : (treesSent c.ch.firstTree (#[sh] : Array TreeShape).toList c.ch.roots
        c.book.trees)[c.book.trees.size]?
          = some
            { shape := sh, number := c.ch.firstTree + c.ch.roots, src := .own c.ch.roots } := by
      show (c.book.trees.push _)[c.book.trees.size]? = _
      rw [Array.getElem?_push_size]
    rw [hnew] at hpub
    cases htree : (partsLaid sent lay c.st.oracles.size c.book.trees.size
        (treesSent c.ch.firstTree (#[sh] : Array TreeShape).toList c.ch.roots c.book.trees))[
          c.book.trees.size]? with
    | none => rw [htree] at hpub; cases hpub
    | some tree =>
      rw [htree] at hpub
      obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj hpub)
      refine ⟨c.book.trees.size, tree, ?_, e2, by rw [e1], by rw [e1]; exact hmain,
        by rw [e1]; exact hmask, fun w hw => ?_⟩
      · rw [hb]
        show (partsLaid _ lay _ _ (treesSent _ lay.shapes.toList _ _))[_]? = _
        rw [h1]
        exact htree
      · have hw' : w < sent.size := by simpa using hw
        rw [hid w hw', hb]
        show (c.book.place ++ _)[w + c.st.oracles.size]? = _
        rw [hp, Array.getElem?_append_right (Nat.le_add_left _ _), Nat.add_sub_cancel,
          Array.getElem?_map, Array.getElem?_range, if_pos hw']
        show some (c.book.trees.size + lay.tree.getD w 0, lay.part.getD w 0) = _
        rw [(ht w hw').1, (ht w hw').2, Nat.add_zero]
  · -- the shapes
    intro w hw
    have hw' : w < sent.size := by simpa using hw
    have hs : ((cB.st.oracles[w + c.st.oracles.size]?).map (·.shape))
        = some (sent[w]).shape := by
      rw [hs, Nat.add_comm, stSent_new, Array.getElem?_eq_getElem hw']
      rfl
    rw [hid w hw']
    cases hx : cB.st.oracles[w + c.st.oracles.size]? with
    | none => rw [hx] at hs; cases hs
    | some x =>
      rw [hx] at hs
      refine ⟨x, rfl, (Option.some.inj hs).trans ?_⟩
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, Array.getElem?_toList,
        Array.getElem?_eq_getElem hw']
      rfl

end OnBytes.Slice

#print axioms OnBytes.Slice.bookSent_keeps
#print axioms OnBytes.Slice.seat_of_sent
#print axioms OnBytes.Slice.treesSent_old
#print axioms OnBytes.Slice.partsLaid_old
#print axioms OnBytes.Slice.admitted_shape
#print axioms OnBytes.Slice.joined_shape
#print axioms OnBytes.Slice.partsLaid_public
#print axioms OnBytes.Slice.shapesKeep_of_map
