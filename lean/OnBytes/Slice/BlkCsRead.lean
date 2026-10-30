-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkCsRead.lean: the symbols that the program reads before a code switch are those of
the three folded words.

After a fold the program holds a claim on three rows that nobody has sent: one is folded from the
main rows, one from the carried mask rows and one from the fresh mask rows. Before the code switch
it reads these rows at drawn positions: it opens the columns of the tree that holds the rows before
the fold, puts their symbols into a main table and a mask table, and folds the tables at the fold's
point (OnBytes/Iop/Fold.lean: `singleRowsRead`). OnBytes/Slice/Stage.lean has the same three rows
as a word of the library's code, `wordMid`, made from the format's columns. This file shows that
the two agree at every listed position.

Main theorems.
 `indexOf_some`        a listed position has a number in the list, and is there.
 `symS_of_cols`        if the program's two tables and its fresh column have the entries of the
                       format's column at each listed position, the symbols read are the long
                       symbols of `wordMid` at the point that the fold's challenges give.
 `readSeat`            what is opened of the oracle messages that are the parts of one tree: words
                       that the view (`Fmt.View`: a proof's rounds and opened columns) shows under
                       the tree's number, and each message's symbols cut out of them.

Not claimed. That the tables have these entries: that depends on how the stage's tree is arranged
and is shown separately for each kind of stage.
-/
import OnBytes.Iop.SymbolLaws
import OnBytes.Slice.BlkCsRun
import OnBytes.Slice.BlkCsSym
import OnBytes.Slice.BlkOpenN
import OnBytes.Slice.BlkSeat

set_option autoImplicit false

namespace OnBytes.Slice

/-! ## A position's number in the list -/

/-- A listed position has a number in the list, and is there. -/
theorem indexOf_some (pos : Positions) (x : ℕ) (hx : x ∈ pos.all) :
    ∃ i, pos.indexOf x = some i ∧ i < pos.all.size ∧ pos.all.getD i 0 = x := by
  unfold Positions.indexOf
  cases h : pos.all.idxOf? x with
  | none => exact absurd hx (Array.idxOf?_eq_none_iff.1 h)
  | some i =>
    rw [Array.idxOf?_eq_map_finIdxOf?_val] at h
    obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 h
    refine ⟨j.val, rfl, j.isLt, ?_⟩
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem j.isLt, Option.getD_some]
    exact (Array.finIdxOf?_eq_some_iff.1 hj).1

/-! ## From the tables to the folded words -/

/-- The main table of a listed position, entry by entry, as the members' columns fill it. -/
def mainAt (L : GroupLayout) (opened : Array (Array Column)) (i : ℕ) : ℕ → E :=
  (List.range L.members.size).foldl
    (fun base w => putAt (L.mainFirst.getD w none) (colB opened w i).main base) fun _ => zeroE

/-- The mask table of a listed position, entry by entry, as the members' columns fill it. -/
def maskAt (L : GroupLayout) (opened : Array (Array Column)) (i : ℕ) : ℕ → E :=
  (List.range L.members.size).foldl
    (fun base w => putAt (L.maskFirst.getD w none) (colB opened w i).mask base) fun _ => zeroE

/-- If the program's two tables and its fresh column have the entries of the format's column at each
listed position, the symbols read are the long symbols of the three folded words. Also asked: two
mask rows, no kept member, the stage's numbers of row bits. -/
theorem symS_of_cols (s : Sg) (old : SingleRows) (pos : Positions) (opened : Array (Array Column))
    (y : Array E) (col : ℕ → Fmt.M1.Col)
    (hsym : singleRowsSymbols old opened pos.all.size = some y) (hm : old.masks = 2)
    (hkept : ∀ w, w < old.layout.members.size → old.layout.kept.getD w false = false)
    (hk : old.layout.k = s.h + s.g) (hh : old.layout.h = s.h)
    (hmain : ∀ i, i < pos.all.size → ∀ b, b < 2 ^ (s.h + s.g) →
      readE (mainAt old.layout opened i b) = vec (col (pos.all.getD i 0)).main b)
    (hmask : ∀ i, i < pos.all.size → ∀ b, b < 2 ^ s.h →
      readE (maskAt old.layout opened i b) = vec (col (pos.all.getD i 0)).mask b)
    (hfresh : ∀ i, i < pos.all.size → ∀ b, b < 2 ^ s.h →
      readV (colB opened old.layout.members.size i).mask b = vec (col (pos.all.getD i 0)).fresh b)
    (x : s.Ps) (hx : x.val ∈ pos.all) (α : s.cMid.Aa) :
    s.cMid.T (wordMid s col (readP _ old.gamma)) x α = symS s old pos y x.val α := by
  obtain ⟨i, hi, hlt, hxi⟩ := indexOf_some pos x.val hx
  obtain ⟨hg, _, _, hall⟩ := singleRowsSymbols_inv old opened _ y (by omega) hsym
  obtain ⟨t, ht, _, y0, _, y1, y2⟩ := hall i hlt
  obtain ⟨z1, z2, _, e1, e2⟩ := tablesAt_inv old.layout opened i t ht hkept
  obtain ⟨zf, y2⟩ := y2 hm
  have hg' : old.gamma.length = s.h + s.g := hg.trans hk
  rw [hh] at y1 y2 zf z2
  rw [hk] at z1
  rcases α with _ | _ | _
  · rw [sym_main s col old.gamma hg' x t.1 z1 fun b hb => by
      unfold readV
      rw [e1 b, ← hxi]
      exact hmain i hlt b hb]
    unfold symS readV
    rw [hi, Option.getD_some, y0]
  · rw [sym_mask s col old.gamma hg' x t.2.1 z2 fun b hb => by
      unfold readV
      rw [e2 b, ← hxi]
      exact hmask i hlt b hb]
    unfold symS readV
    rw [hi, Option.getD_some, y1 (by omega)]
  · rw [sym_fresh s col old.gamma hg' x _ zf fun b hb => by
      rw [← hxi]
      exact hfresh i hlt b hb]
    unfold symS readV
    rw [hi, Option.getD_some, y2]

/-! ## What is opened of the oracle messages that are the parts of one tree (`Seat`) -/

/-- What is read of the oracle messages that are the parts of one tree, on a view. The tree's
columns at the listed positions are words cs. Under every function that the view shows for the
tree's number these are the function's values. Each message's symbols are cut out of these
words. -/
theorem readSeat (V : Fmt.View) (ids : List ℕ) (pos : Positions) (a a' : Ctx)
    (opened : Array (Array Column)) (n : ℕ) (shapes : List OracleShape) (hv : OnView V a)
    (hrd : (Blk.readOpened ids.toArray pos).Yields a opened a') (hne : 0 < ids.length)
    (seat : Seat a ids n pos.logN shapes) :
    ∃ (tree : Tree) (cs : Array (Array F)),
      tree.shape.mainSymbols = (shapes.map fun s => s.mainRows * s.mainDeg).toArray ∧
      tree.shape.maskSymbols = (shapes.map fun s => s.maskRows * 3).toArray ∧
      cs.size = pos.all.size ∧
      (∀ f, Shows V n f → ∀ i, i < pos.all.size →
        f (pos.all.getD i 0) = some (cs.getD i #[]).toList) ∧
      ∀ p, p < ids.length → ∃ x : Oracle, x.shape = shapes.getD p default ∧
        ∀ i, i < pos.all.size →
          colB opened p i = Blk.columnOf x (mainSkip tree p) (maskSkip tree p) (cs.getD i #[]) := by
  obtain ⟨t, tree, h1, h2, h3, h4, h5, h6⟩ := seat.tree
  have hid : ∀ p (h : p < ids.toArray.size), ids.toArray[p] = ids.getD p 0 := fun p h => by
    rw [List.getElem_toArray, List.getD_eq_getElem _ _ (by simpa using h)]
  obtain ⟨cs, hs, hop, _, _, _, hcol⟩ := readParts ids.toArray t pos a a' opened hv.dry hrd tree
    (by rw [List.size_toArray]; exact hne)
    (fun p h => by
      rw [hid p h]
      exact h6 p (by simpa using h)) h1 h3
  refine ⟨tree, cs, h4, h5, hs, fun f hf i hi => ?_, fun p hp => ?_⟩
  · have hmem := viewColumns_at (tree.number - a.ch.firstTree) pos.all cs hs i hi
    have hV := hv.opened _ (by rw [hop]; exact List.mem_append_left _ hmem)
    exact hf _ hV (by
      show tree.number - a.ch.firstTree = n
      rw [hv.first, h2, Nat.sub_zero])
  · obtain ⟨x, hx, hsh⟩ := seat.shape p hp
    have hp' : p < ids.toArray.size := by rw [List.size_toArray]; exact hp
    exact ⟨x, hsh, fun i hi => hcol p hp' x (by rw [hid p hp']; exact hx) i hi⟩

end OnBytes.Slice

#print axioms OnBytes.Slice.indexOf_some
#print axioms OnBytes.Slice.symS_of_cols
#print axioms OnBytes.Slice.readSeat
