-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkOpenN.lean: what the program reads of the oracle messages that are the parts of one
tree.

`Blk.readOpened` opens the trees of some oracle messages at a list of positions. The law on it
(OnBytes/Iop/OpenLaws.lean: `readOpened_inv`) speaks of any number of trees. In a proximity test the
oracle messages that are read together are the parts of one tree, in the order of the parts, and the
tree is as long as the list's range. This file brings the law to that case.

Main definitions: `mainSkip`, `maskSkip` (the words at which a part's symbols begin in a column).
Main theorems.
 `list_mapM_inv`, `array_mapM_inv`   a list of values that may be missing, if none is missing.
 `symbolsOf_inv`  the symbols of one oracle message out of the columns of its tree.
 `viewColumns_at` a column of a tree is among the columns as a view holds them.
 `listOf_const`   the list without repeats of a list that holds one number alone.
 `readParts`      the view's next opened columns were the tree's, at the list's positions; what is
                  left of them; the symbols of part p are cut out of these columns at the words
                  where part p begins; all else stays as it was.
Not claimed. Nothing on a tree that is shorter than the list's range. Nothing on what the columns
hold.
-/
import OnBytes.Iop.OpenLaws

set_option autoImplicit false

namespace OnBytes.Slice

/-! ## A list of values that may be missing -/

/-- If every member of a list has a value, the values are in the members' order. -/
theorem list_mapM_inv {α β : Type} (f : α → Option β) : ∀ (l : List α) (out : List β),
    l.mapM f = some out → out.length = l.length ∧ ∀ (i : Nat) (h : i < l.length), f l[i] = out[i]?
  | [], out, h => by
    rw [List.mapM_nil] at h
    obtain rfl : [] = out := Option.some.inj h
    exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | a :: l, out, h => by
    rw [List.mapM_cons] at h
    cases hb : f a with
    | none =>
      rw [hb] at h
      cases h
    | some b =>
      cases hbs : l.mapM f with
      | none =>
        rw [hb, hbs] at h
        cases h
      | some bs =>
        rw [hb, hbs] at h
        obtain rfl : b :: bs = out := Option.some.inj h
        obtain ⟨h1, h2⟩ := list_mapM_inv f l bs hbs
        refine ⟨congrArg (· + 1) h1, fun i hi => ?_⟩
        cases i with
        | zero => exact hb
        | succ i => exact h2 i (Nat.lt_of_succ_lt_succ hi)

/-- The same for arrays. -/
theorem array_mapM_inv {α β : Type} (f : α → Option β) (l : Array α) (out : Array β)
    (h : l.mapM f = some out) :
    out.size = l.size ∧ ∀ (i : Nat) (hi : i < l.size), f l[i] = out[i]? := by
  rw [Array.mapM_eq_mapM_toList] at h
  obtain ⟨o', h1, h2⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨k1, k2⟩ := list_mapM_inv f l.toList o' h1
  subst h2
  refine ⟨k1, fun i hi => ?_⟩
  have := k2 i hi
  simpa using this

/-! ## One oracle message in a tree -/

/-- The word at which the main symbols of part p of a tree begin in a leaf's column. -/
def mainSkip (tree : Tree) (p : Nat) : Nat := (tree.shape.mainSymbols.extract 0 p).foldl (· + ·) 0

/-- The word at which the mask symbols of part p of a tree begin in a leaf's column. -/
def maskSkip (tree : Tree) (p : Nat) : Nat :=
  tree.shape.mainWidth + (tree.shape.maskSymbols.extract 0 p).foldl (· + ·) 0

/-- The symbols of one oracle message out of the columns of its tree, where the tree is as long as
the list's range. -/
theorem symbolsOf_inv (S : Statement) (B : TreeBook) (pos : Positions) (t : Nat) (own : Array Nat)
    (cs : Array (Array F)) (o p : Nat) (tree : Tree) (x : Oracle) (out : Array Column)
    (htr : B.trees[t]? = some tree) (hx : S.oracles[o]? = some x)
    (hlog : tree.shape.logN = pos.logN) (hs : cs.size = pos.all.size)
    (h : Blk.symbolsOf S B pos [(t, own, cs)] o (t, p) = some out) :
    ∀ i, i < pos.all.size →
      out.getD i {} = Blk.columnOf x (mainSkip tree p) (maskSkip tree p) (cs.getD i #[]) := by
  intro i hi
  unfold Blk.symbolsOf at h
  simp only [htr, hx, List.find?_cons, beq_self_eq_true, Option.bind_eq_bind, Option.bind_some,
    hlog, if_true] at h
  obtain ⟨k1, k2⟩ := array_mapM_inv _ _ _ h
  have k3 := k2 i (by rw [Array.size_range]; exact hi)
  have hic : i < cs.size := by rw [hs]; exact hi
  rw [Array.getElem_range, Array.getElem?_eq_getElem hic] at k3
  rw [Array.getD_eq_getD_getElem?, ← k3, Array.getD_eq_getD_getElem?,
    Array.getElem?_eq_getElem hic]
  rfl

/-! ## The parts of one tree -/

/-- A column of a tree is among the columns as a view holds them. -/
theorem viewColumns_at (key : Nat) (xs : Array Nat) (cs : Array (Array F)) (hs : cs.size = xs.size)
    (i : Nat) (hi : i < xs.size) :
    (key, xs.getD i 0, (cs.getD i #[]).toList) ∈ viewColumns key xs cs := by
  have hic : i < cs.size := by rw [hs]; exact hi
  unfold viewColumns
  refine List.mem_map.2 ⟨(xs.getD i 0, cs.getD i #[]), ?_, rfl⟩
  have hz : i < (xs.toList.zip cs.toList).length := by
    rw [List.length_zip, Array.length_toList, Array.length_toList, hs, Nat.min_self]
    exact hi
  have hm := List.getElem_mem hz
  rw [List.getElem_zip] at hm
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi,
    Array.getElem?_eq_getElem hic]
  simpa using hm

/-- The list without repeats of a list that holds one number alone. -/
theorem listOf_const (t : Nat) : ∀ l : List Nat, l ≠ [] → (∀ x ∈ l, x = t) → Fmt.listOf l = [t]
  | [], h, _ => absurd rfl h
  | [x], _, h => by
    rw [h x (List.mem_singleton.2 rfl)]
    rfl
  | x :: y :: l, _, h => by
    have ih := listOf_const t (y :: l) (List.cons_ne_nil _ _) fun z hz =>
      h z (List.mem_cons_of_mem _ hz)
    show Fmt.insertIntoIncreasingList x (Fmt.listOf (y :: l)) = [t]
    rw [ih, h x List.mem_cons_self]
    simp [Fmt.insertIntoIncreasingList]

/-- What is read of the oracle messages that are the parts of one tree, at a list of the tree's
own range. The view's next opened columns were the tree's, at the list's positions; the symbols of
every message are cut out of these columns; all else stays as it was. -/
theorem readParts (ids : Array Nat) (t : Nat) (pos : Positions) (a c' : Ctx)
    (opened : Array (Array Column)) (hda : a.ch.dry = false)
    (hrd : (Blk.readOpened ids pos).Yields a opened c') (tree : Tree) (hne : 0 < ids.size)
    (hpl : ∀ p (h : p < ids.size), a.book.place[ids[p]]? = some (t, p))
    (htr : a.book.trees[t]? = some tree) (hlog : tree.shape.logN = pos.logN) :
    ∃ cs : Array (Array F), cs.size = pos.all.size ∧
      a.ch.opened = viewColumns (tree.number - a.ch.firstTree) pos.all cs ++ c'.ch.opened ∧
      Blk.Frame a c' ∧ Blk.BookKept a.book c'.book ∧ opened.size = ids.size ∧
      ∀ p (h : p < ids.size) x, a.st.oracles[ids[p]]? = some x → ∀ i, i < pos.all.size →
        (opened.getD p #[]).getD i {} =
          Blk.columnOf x (mainSkip tree p) (maskSkip tree p) (cs.getD i #[]) := by
  obtain ⟨places, cols, h1, h2, h3, h4, h5, fr, bk⟩ := Blk.readOpened_inv _ _ _ _ _ hda hrd
  obtain ⟨z1, z2⟩ := array_mapM_inv _ _ _ h1
  -- every message's place
  have hplace : ∀ p (h : p < ids.size), places[p]? = some (t, p) := fun p h =>
    (z2 p h).symm.trans (hpl p h)
  -- one tree was opened
  have e3 : Fmt.listOf (places.map (·.1)).toList = [t] := by
    refine listOf_const t _ ?_ ?_
    · intro he
      have hl := congrArg List.length he
      rw [Array.length_toList, Array.size_map, z1, List.length_nil] at hl
      omega
    · intro x hx
      simp only [Array.toList_map, List.mem_map, Array.mem_toList_iff] at hx
      obtain ⟨q, hq, rfl⟩ := hx
      obtain ⟨p, hp, rfl⟩ := Array.mem_iff_getElem.1 hq
      have := hplace p (by rw [← z1]; exact hp)
      rw [Array.getElem?_eq_getElem hp] at this
      rw [Option.some.inj this]
  rw [e3] at h3
  obtain ⟨⟨t', own, cs⟩, rfl⟩ : ∃ y, cols = [y] := by
    cases cols with
    | nil => cases h3
    | cons y l =>
      cases l with
      | nil => exact ⟨y, rfl⟩
      | cons z l' => simp at h3
  obtain rfl : t = t' := (List.cons.inj h3).1.symm
  obtain ⟨tree', k1, _, k3, k4⟩ := h4 _ (List.mem_singleton.2 rfl)
  obtain rfl : tree = tree' := Option.some.inj (htr.symm.trans k1)
  have hown : own = pos.all := by
    have k3' : own = Blk.ownList tree pos := k3
    rw [k3']
    unfold Blk.ownList
    rw [hlog, if_pos (beq_self_eq_true _)]
  subst hown
  have hcs : cs.size = pos.all.size := k4
  have hkey : Blk.treeKey a.book a.ch.firstTree t = tree.number - a.ch.firstTree := by
    unfold Blk.treeKey
    rw [htr]
    rfl
  rw [List.flatMap_singleton, hkey] at h2
  obtain ⟨w1, w2⟩ := array_mapM_inv _ _ _ h5
  have hzs : (ids.zip places).size = ids.size := by
    rw [Array.size_zip, z1, Nat.min_self]
  refine ⟨cs, hcs, h2, fr, bk, w1.trans hzs, ?_⟩
  intro p hp x hx i hi
  have hp' : p < places.size := by rw [z1]; exact hp
  have q1 := w2 p (by rw [hzs]; exact hp)
  rw [Array.getElem_zip] at q1
  have hpp : places[p] = (t, p) := by
    have := hplace p hp
    rw [Array.getElem?_eq_getElem hp'] at this
    exact Option.some.inj this
  have hop : p < opened.size := by rw [w1, hzs]; exact hp
  rw [Array.getElem?_eq_getElem hop] at q1
  have q2 : Blk.symbolsOf a.st a.book pos [(t, pos.all, cs)] ids[p] (t, p) = some opened[p] := by
    rw [← hpp]
    exact q1
  have eo : opened.getD p #[] = opened[p] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hop]
    rfl
  rw [eo]
  exact symbolsOf_inv _ _ _ _ _ _ _ _ _ _ _ htr hx hlog hcs q2 i hi

end OnBytes.Slice

#print axioms OnBytes.Slice.symbolsOf_inv
#print axioms OnBytes.Slice.readParts
#print axioms OnBytes.Slice.list_mapM_inv
#print axioms OnBytes.Slice.array_mapM_inv
#print axioms OnBytes.Slice.viewColumns_at
#print axioms OnBytes.Slice.listOf_const
