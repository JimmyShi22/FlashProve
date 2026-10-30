-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/ReadYes.lean: THE READING OF THE OLD ROWS AT A SWITCH RETURNS (Tw.L9.readOld,
Johnson/Top/H0/Tw/L9/Switch.lean), from ReadFront (Johnson/Prover/Link/ReadFront.lean): the book
behind as a term (one list more at the tree), NO COLUMN LEFT, and as many symbols as the listed
positions times the rows. It is the converse, at one tree, of the laws that read a yes (readOld_inv,
readPartsP: Johnson/Desc/K12/Law/SwRead.lean).

Main names (namespace Johnson.Prover.Link).
  list_mapM_some, array_mapM_some   a loop in Option returns its members' values, by number.
  openOne_yes   G8 to G12: one tree is opened at the list; all dealt columns are taken.
  partCols, symbolsAt_yes, partCols_at   G15: what a part shows at the listed positions; its sizes.
  read_yes   THE STATEMENT (Spec.read_yes).

By: listOfT_eq (OnBytes/Chain/Draws.lean) · listOf_const (OnBytes/Slice/BlkOpenN.lean) ·
rowsSymbols_some (Johnson/Prover/Link/ReadRows.lean).

Limits. That the reading returns: WHAT the symbols are is other files' (the values' half), which
take any yes. The symbols y stay behind "there is". ReadFront is a premise.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.ReadFront
import Johnson.Prover.Link.ReadRows
import OnBytes.Slice.BlkOpenN
import OnBytes.Chain.Draws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Slice
open VerifiableInference.Desc

/-! ## A loop that returns -/

/-- Where each member's value is there, the loop returns them, by number. -/
theorem list_mapM_some {α β : Type} (f : α → Option β) (g : Nat → β) :
    ∀ (l : List α) (off : Nat), (∀ k (hk : k < l.length), f l[k] = some (g (off + k))) →
      l.mapM f = some ((List.range' off l.length).map g)
  | [], _, _ => rfl
  | a :: l, off, h => by
    have h0 : f a = some (g off) := h 0 (Nat.zero_lt_succ _)
    have ih := list_mapM_some f g l (off + 1) fun k hk => by
      have := h (k + 1) (Nat.succ_lt_succ hk)
      rw [List.getElem_cons_succ] at this
      rw [this]
      congr 2
      omega
    rw [List.mapM_cons, h0, ih]
    rfl

/-- The same for arrays. -/
theorem array_mapM_some {α β : Type} (f : α → Option β) (g : Nat → β) (xs : Array α)
    (h : ∀ k (hk : k < xs.size), f xs[k] = some (g k)) :
    xs.mapM f = some ((List.range' 0 xs.size).map g).toArray := by
  rw [Array.mapM_eq_mapM_toList, list_mapM_some f g xs.toList 0 fun k hk => by
    rw [Nat.zero_add]
    simpa using h k (by simpa using hk)]
  simp

/-! ## One tree is opened -/

/-- **[G8]–[G12].** -/
theorem openOne_yes (S : Statement) (F : Nat) (pos : Positions) (B : TreeBook) (t : Nat)
    (tr : Tree) (op : List Tw.L9.Col) (hB : B.trees[t]? = some tr) (h9 : sharesOk S tr = true)
    (h10 : (!tr.oneList || tr.lists == 0) = true) (hl : tr.shape.logN = pos.logN)
    (hn : op.length = pos.all.size)
    (hs : Own.colsStand (tr.number - F) (tr.shape.mainWidth + tr.shape.maskWidth) op
      pos.all.toList = true) :
    Tw.L9.openOne S F pos B t (B, op, #[]) =
      .ok (bookRead B t, [], #[(t, pos.all, (op.map fun y => y.2.2.toArray).toArray)]) := by
  have hown : Blk.ownList tr pos = pos.all := by
    unfold Blk.ownList
    rw [hl, if_pos (beq_self_eq_true _)]
  have e9 : (!sharesOk S tr) = false := by rw [h9]; rfl
  unfold Tw.L9.openOne
  simp only [hB, h10, hl, hown, Bool.not_true, Bool.false_eq_true, if_false,
    ← hn, List.take_length, List.drop_length, beq_self_eq_true, Bool.true_and]
  rw [if_neg (by
      show ¬ (!sharesOk S tr) = true
      rw [e9]
      exact Bool.false_ne_true),
    if_neg (by simp), if_pos hs]
  rfl

/-! ## A message's symbols are found -/

/-- What part p of a tree shows at the listed positions, out of the tree's columns cs. -/
def partCols (tr : Tree) (x : OnBytes.Oracle) (cs : Array (Array F)) (n p : Nat) : Array Column :=
  ((List.range' 0 n).map fun k => Blk.columnOf x
    ((tr.shape.mainSymbols.extract 0 p).foldl (· + ·) 0)
    (tr.shape.mainWidth + (tr.shape.maskSymbols.extract 0 p).foldl (· + ·) 0)
    (cs.getD k #[])).toArray

/-- **[G15]** at the one opened tree, which is as long as the list's range. -/
theorem symbolsAt_yes (S : Statement) (B : TreeBook) (pos : Positions) (t p o : Nat) (tr : Tree)
    (x : OnBytes.Oracle) (cs : Array (Array F)) (hB : B.trees[t]? = some tr)
    (hx : S.oracles[o]? = some x) (hl : tr.shape.logN = pos.logN) (hn : cs.size = pos.all.size) :
    Own.symbolsAt S B pos [(t, pos.all, cs)] o (t, p) =
      some (partCols tr x cs pos.all.size p) := by
  unfold Own.symbolsAt partCols
  simp only [hB, hx, List.find?_cons, beq_self_eq_true]
  rw [list_mapM_some _ (fun k => Blk.columnOf x
      ((tr.shape.mainSymbols.extract 0 p).foldl (· + ·) 0)
      (tr.shape.mainWidth + (tr.shape.maskSymbols.extract 0 p).foldl (· + ·) 0)
      (cs.getD k #[])) (List.range pos.all.size) 0 fun k hk => ?_]
  · rw [List.length_range]
    rfl
  · have hk' : k < cs.size := by
      rw [hn]
      simpa using hk
    rw [List.getElem_range, Nat.zero_add, hl]
    simp only [Own.whereOpened, beq_self_eq_true, if_true, Option.bind_some]
    rw [Array.getElem?_eq_getElem hk', Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk']
    rfl

/-- A column of a part: as many symbols as the message has rows. -/
theorem partCols_at (tr : Tree) (x : OnBytes.Oracle) (cs : Array (Array F)) (n p j : Nat)
    (hj : j < n) :
    ∃ col, (partCols tr x cs n p)[j]? = some col ∧ col.main.size = x.shape.mainRows ∧
      col.mask.size = x.shape.maskRows := by
  refine ⟨Blk.columnOf x ((tr.shape.mainSymbols.extract 0 p).foldl (· + ·) 0)
    (tr.shape.mainWidth + (tr.shape.maskSymbols.extract 0 p).foldl (· + ·) 0)
    (cs.getD (0 + 1 * j) #[]), ?_, ?_, ?_⟩
  · unfold partCols
    rw [List.getElem?_toArray, List.getElem?_map, List.getElem?_range' hj]
    rfl
  · simp [Blk.columnOf]
  · simp [Blk.columnOf]

/-! ## The reading -/

/-- **THE READING OF THE OLD ROWS RETURNS**: the book with one list more at the tree, no column
left, and as many symbols as the listed positions times the rows. -/
theorem read_yes : Spec.read_yes := by
  intro i pos t tr H
  have hids : singleRowsOracles i.old = i.old.layout.members.push i.old.fresh := by
    unfold singleRowsOracles
    rw [H.masks]
    rfl
  have hsz : (singleRowsOracles i.old).size = i.old.layout.members.size + 1 := by
    rw [hids, Array.size_push]
  -- [G13]
  have hP := array_mapM_some (fun o => i.book.place[o]?) (fun p => (t, p))
    (singleRowsOracles i.old) H.place
  -- one tree
  have hT : listOfT ((((List.range' 0 (singleRowsOracles i.old).size).map
      fun p => (t, p)).toArray.map (·.1)).toList) = [t] := by
    rw [listOfT_eq]
    refine listOf_const t _ ?_ ?_
    · rw [hsz]
      simp [List.range'_succ]
    · intro x hx
      simp only [List.map_toArray, List.map_map, List.mem_map] at hx
      obtain ⟨_, _, rfl⟩ := hx
      rfl
  -- [G8]–[G12]
  have hO := openOne_yes i.st i.firstTree pos i.book t tr i.opened H.inBook H.shares H.once H.log
    H.dealt H.stand
  have hcs : ((i.opened.map fun y => y.2.2.toArray).toArray).size = pos.all.size := by
    rw [List.size_toArray, List.length_map]
    exact H.dealt
  -- [G15]
  have hzs : ((singleRowsOracles i.old).zip (((List.range' 0 (singleRowsOracles i.old).size).map
      fun p => (t, p)).toArray)).size = (singleRowsOracles i.old).size := by
    simp
  have hS := array_mapM_some
    (fun y : Nat × Nat × Nat => Own.symbolsAt i.st i.book pos
      [(t, pos.all, (i.opened.map fun y => y.2.2.toArray).toArray)] y.1 y.2)
    (fun p => partCols tr ((i.st.oracles[(singleRowsOracles i.old).getD p 0]?).getD default)
      (i.opened.map fun y => y.2.2.toArray).toArray pos.all.size p)
    ((singleRowsOracles i.old).zip (((List.range' 0 (singleRowsOracles i.old).size).map
      fun p => (t, p)).toArray)) fun k hk => by
      have hk' : k < (singleRowsOracles i.old).size := by rw [← hzs]; exact hk
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (H.there k hk')
      have e1 : (singleRowsOracles i.old).getD k 0 = (singleRowsOracles i.old)[k] := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk']
        rfl
      rw [Array.getElem_zip]
      dsimp only
      rw [e1, hx]
      simp only [List.getElem_toArray, List.getElem_map, List.getElem_range', Nat.zero_add,
        Nat.one_mul, Option.getD_some]
      exact symbolsAt_yes i.st i.book pos t k _ tr x _ H.inBook hx H.log hcs
  rw [hzs] at hS
  -- [G16]
  have hop : ∀ w, w < (singleRowsOracles i.old).size →
      (((List.range' 0 (singleRowsOracles i.old).size).map fun p => partCols tr
        ((i.st.oracles[(singleRowsOracles i.old).getD p 0]?).getD default)
        (i.opened.map fun y => y.2.2.toArray).toArray pos.all.size p).toArray)[w]? =
      some (partCols tr ((i.st.oracles[(singleRowsOracles i.old).getD w 0]?).getD default)
        (i.opened.map fun y => y.2.2.toArray).toArray pos.all.size w) := by
    intro w hw
    rw [List.getElem?_toArray, List.getElem?_map, List.getElem?_range' hw]
    simp
  obtain ⟨y, hy, hys⟩ := rowsSymbols_some i.old (n := pos.all.size) (hs := H.shape)
    (hm := H.masks) (hr := H.keptRows) (hk := H.noKept)
    (opened := ((List.range' 0 (singleRowsOracles i.old).size).map fun p => partCols tr
        ((i.st.oracles[(singleRowsOracles i.old).getD p 0]?).getD default)
        (i.opened.map fun y => y.2.2.toArray).toArray pos.all.size p).toArray)
    fun j hj => by
      refine ⟨fun w hw => ?_, ?_⟩
      · have hw' : w < (singleRowsOracles i.old).size := by rw [hsz]; omega
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (H.there w hw')
        have e1 : (singleRowsOracles i.old).getD w 0 = i.old.layout.members.getD w 0 := by
          rw [hids, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
            Array.getElem?_push_lt hw]
          simp [hw]
        have e2 : (singleRowsOracles i.old)[w] = i.old.layout.members.getD w 0 := by
          rw [← e1, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hw']
          rfl
        rw [e2] at hx
        obtain ⟨col, hc, sM, sZ⟩ := partCols_at tr x
          (i.opened.map fun y => y.2.2.toArray).toArray pos.all.size w j hj
        refine ⟨col, ?_, ?_, ?_⟩
        · rw [hop w hw', e1, hx]
          exact hc
        · rw [sZ]
          rcases Nat.eq_zero_or_pos x.shape.maskRows with h0 | h0
          · exact Or.inl h0
          · exact Or.inr (H.roomZ w x hw hx h0)
        · rw [sM]
          rcases Nat.eq_zero_or_pos x.shape.mainRows with h0 | h0
          · exact Or.inl h0
          · exact Or.inr (H.roomM w x hw hx h0)
      · have hw' : i.old.layout.members.size < (singleRowsOracles i.old).size := by
          rw [hsz]; omega
        obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (H.there _ hw')
        have e2 : (singleRowsOracles i.old)[i.old.layout.members.size] = i.old.fresh := by
          simp [hids]
        have e1 : (singleRowsOracles i.old).getD i.old.layout.members.size 0 = i.old.fresh := by
          rw [← e2, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hw']
          rfl
        rw [e2] at hx
        obtain ⟨col, hc, -, sZ⟩ := partCols_at tr x
          (i.opened.map fun y => y.2.2.toArray).toArray pos.all.size
          i.old.layout.members.size j hj
        refine ⟨col, ?_, sZ.trans (H.fresh x hx)⟩
        rw [hop _ hw', e1, hx]
        exact hc
  refine ⟨y, ?_, hys⟩
  unfold Tw.L9.readOld
  simp only [hP, hT, List.all_cons, List.all_nil, Bool.and_true, H.inBook, Option.map_some,
    Option.getD_some, H.parts, Bool.not_true, Bool.false_eq_true, if_false, List.foldlM_cons,
    List.foldlM_nil, hO, bind, Except.bind, pure, Except.pure]
  rw [hS]
  dsimp only
  rw [hy]

end Johnson.Prover.Link
