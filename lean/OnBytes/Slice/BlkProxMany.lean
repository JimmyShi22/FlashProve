-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkProxMany.lean: what the program reads of oracle messages that lie in several trees,
some of them shorter than the list's range.

At the first code switch of a proximity test the program reads the group's members and the fold's
fresh mask by one call (OnBytes/Iop/Ground.lean: Blk.readOpened). In a link's chain they are the
parts of one tree as long as the range of the positions (OnBytes/Slice/BlkOpenN.lean: readParts).
In a key's chains they lie in up to three trees, some of them shorter than the range: such a tree is
opened at the draws modulo its length. The call opens the trees one after the other, by their places
in the book. This file goes by that order (OnBytes/Slice/BlkProxSeg.lean): if what is left to be
read begins with the trees' segments in turn, each oracle message's symbols at a listed position are
cut from its tree's column there, and what comes after the segments is left.

Main definitions.
  placeIn     the position of a tree of 2^logT leaves that belongs to a position x of a range of
              2^logN: x itself if the tree is as long as the range, else x modulo the tree's length.
  ownAt       the list at which a tree of a given depth is opened under a list of positions.
  expCols     the segments of the trees at some places of the book, in turn.
Main theorems.
  idxOf_some     what Array.idxOf? returns is a place that holds the value.
  symbolsOf_at   the program's cut of one oracle message's symbols out of the opened trees' columns.
  flatMap_cut    two lists made of pieces of equal lengths, with a rest each, are equal only if the
                 pieces and the rests are.
  readMany_seg   the statement above.

Not claimed. Nothing on how a column's words are read in the field.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BlkProxSeg

set_option autoImplicit false

namespace OnBytes.Slice.ProxRun

/-- The position of a tree of 2^logT leaves that belongs to the position x of a range of 2^logN
positions. -/
def placeIn (logT logN x : Nat) : Nat := if logT = logN then x else x % 2 ^ logT

/-- What Array.idxOf? returns is a place of the array that holds the value. -/
theorem idxOf_some (xs : Array Nat) (v i : Nat) (h : xs.idxOf? v = some i) :
    i < xs.size ∧ xs.getD i 0 = v := by
  rw [Array.idxOf?_eq_map_finIdxOf?_val] at h
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.1 h
  refine ⟨j.isLt, ?_⟩
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem j.isLt, Option.getD_some]
  exact (Array.finIdxOf?_eq_some_iff.1 hj).1

/-- The program's cut of one oracle message's symbols out of the opened trees' columns. mine: the
entry of the message's tree among the opened trees. At each listed position the symbols are cut from
a column of that entry: the column with the position's number, or, for a shorter tree, the column at
the position modulo the tree's length. -/
theorem symbolsOf_at (S : Statement) (B : TreeBook) (pos : Positions)
    (cols : List (Nat × Array Nat × Array (Array F))) (o t p : Nat) (tree : Tree) (x : Oracle)
    (out : Array Column) (mine : Nat × Array Nat × Array (Array F))
    (htr : B.trees[t]? = some tree) (hx : S.oracles[o]? = some x)
    (hfind : cols.find? (·.1 == t) = some mine)
    (h : Blk.symbolsOf S B pos cols o (t, p) = some out) (i : Nat) (hi : i < pos.all.size) :
    ∃ (here : Nat) (c : Array F),
      (if tree.shape.logN == pos.logN then some i
        else mine.2.1.idxOf? (pos.all.getD i 0 % 2 ^ tree.shape.logN)) = some here ∧
      mine.2.2[here]? = some c ∧
      out.getD i {} = Blk.columnOf x (mainSkip tree p) (maskSkip tree p) c := by
  unfold Blk.symbolsOf at h
  simp only [htr, hx, hfind, Option.bind_eq_bind, Option.bind_some] at h
  obtain ⟨k1, k2⟩ := array_mapM_inv _ _ _ h
  have hr : i < (Array.range pos.all.size).size := by rw [Array.size_range]; exact hi
  have k3 := k2 i hr
  have ho : i < out.size := by rw [k1]; exact hr
  rw [Array.getElem_range, Array.getElem?_eq_getElem ho] at k3
  have eo : out.getD i {} = out[i] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ho, Option.getD_some]
  rw [eo]
  by_cases hl : (tree.shape.logN == pos.logN) = true
  · rw [if_pos hl] at k3 ⊢
    obtain ⟨c, h2, k5⟩ := Option.bind_eq_some_iff.1 k3
    exact ⟨i, c, rfl, h2, (Option.some.inj k5).symm⟩
  · rw [if_neg hl] at k3 ⊢
    obtain ⟨here, h1, k4⟩ := Option.bind_eq_some_iff.1 k3
    obtain ⟨c, h2, k5⟩ := Option.bind_eq_some_iff.1 k4
    exact ⟨here, c, h1, h2, (Option.some.inj k5).symm⟩

/-- Two lists made of pieces of equal lengths, with a rest each, are equal only if the pieces and
the rests are. -/
theorem flatMap_cut {α γ : Type} (f1 f2 : α → List γ) : ∀ (l : List α) (r1 r2 : List γ),
    (∀ a ∈ l, (f1 a).length = (f2 a).length) → l.flatMap f1 ++ r1 = l.flatMap f2 ++ r2 →
    (∀ a ∈ l, f1 a = f2 a) ∧ r1 = r2
  | [], _, _, _, h => ⟨fun _ hm => absurd hm List.not_mem_nil, h⟩
  | a :: l, r1, r2, hl, h => by
    rw [List.flatMap_cons, List.flatMap_cons, List.append_assoc, List.append_assoc] at h
    obtain ⟨e1, e2⟩ := List.append_inj h (hl a List.mem_cons_self)
    obtain ⟨i1, i2⟩ := flatMap_cut f1 f2 l r1 r2 (fun b hb => hl b (List.mem_cons_of_mem _ hb)) e2
    refine ⟨fun b hb => ?_, i2⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · exact e1
    · exact i1 b hb

/-- The list at which a tree of 2^logT leaves is opened under a list of positions: the list itself,
or for a shorter tree the list of the draws modulo the tree's length. -/
def ownAt (logT : Nat) (pos : Positions) : Array Nat :=
  if logT == pos.logN then pos.all
  else (listOfT (pos.draws.map (· % 2 ^ logT)).toList).toArray

/-- The program's list for a tree looks at the tree's depth alone. -/
theorem ownList_eq (T : Tree) (pos : Positions) : Blk.ownList T pos = ownAt T.shape.logN pos := rfl

/-- The segments of the trees at the places ts of the book, in turn, each at its own list under the
list of positions pos. key t, log t: the key and the depth of the tree at the place t. g t: the
words of a column of that tree. -/
def expCols (pos : Positions) (key log : Nat → Nat) (g : Nat → Nat → Option (List UInt64))
    (ts : List Nat) : Cols :=
  ts.flatMap fun t => segOf (key t) (ownAt (log t) pos).toList (g t)

/-- What is read of oracle messages in several trees. ids: the oracle messages asked for. ts:
the places of their trees in the book (by hts: each once, increasing). If what is left to be read
begins with the segments of these trees in turn, then R, which comes after them, is left; and the
symbols of the oracle message number w of ids, which is o, part p of the tree at the place t, are
cut at each listed position from a value of g t. -/
theorem readMany_seg (ids : Array Nat) (pos : Positions) (out : Array (Array Column)) (a a' : Ctx)
    (hd : a.ch.dry = false) (hrd : (Blk.readOpened ids pos).Yields a out a')
    (key log : Nat → Nat) (g : Nat → Nat → Option (List UInt64)) (R : Cols) (ts : List Nat)
    (hts : ∀ places, (ids.mapM fun o => a.book.place[o]?) = some places →
      Fmt.listOf (places.map (·.1)).toList = ts)
    (hbk : ∀ t ∈ ts, ∀ T, a.book.trees[t]? = some T →
      T.number - a.ch.firstTree = key t ∧ T.shape.logN = log t)
    (hop : a.ch.opened = expCols pos key log g ts ++ R)
    (hin : ∀ t ∈ ts, ∀ x ∈ (ownAt (log t) pos).toList, (g t x).isSome = true) :
    a'.ch.opened = R ∧
    ∀ (w o t p : Nat) (T : Tree) (x : Oracle), ids[w]? = some o →
      a.book.place[o]? = some (t, p) → a.book.trees[t]? = some T → a.st.oracles[o]? = some x →
      ∀ i, i < pos.all.size →
        ∃ cw : Array OnBytes.F,
          g t (placeIn T.shape.logN pos.logN (pos.all.getD i 0)) = some cw.toList ∧
          colB out w i = Blk.columnOf x (mainSkip T p) (maskSkip T p) cw := by
  obtain ⟨places, cols, h1, h2, h3, h4, h5, _, _⟩ := Blk.readOpened_inv _ _ _ _ _ hd hrd
  have ets := hts places h1
  have hmts : ∀ y ∈ cols, y.1 ∈ ts := fun y hy => by
    rw [← ets, ← h3]
    exact List.mem_map_of_mem hy
  -- segment by segment
  have hexp : expCols pos key log g ts = cols.flatMap fun y =>
      segOf (key y.1) (ownAt (log y.1) pos).toList (g y.1) := by
    unfold expCols
    rw [← ets, ← h3, List.flatMap_map]
  rw [hexp] at hop
  obtain ⟨hseg, hR⟩ := flatMap_cut _ _ cols _ _ (fun y hy => by
    obtain ⟨T, k1, _, k3, k4⟩ := h4 y hy
    obtain ⟨_, b2⟩ := hbk y.1 (hmts y hy) T k1
    unfold viewColumns segOf
    rw [List.length_map, List.length_map, List.length_zip, Array.length_toList,
      Array.length_toList, Array.length_toList, k4, Nat.min_self, k3, ownList_eq, b2])
    (h2.symm.trans hop)
  refine ⟨hR, ?_⟩
  intro w o t p T x hw hpl hT hx i hi
  obtain ⟨z1, z2⟩ := array_mapM_inv _ _ _ h1
  obtain ⟨hwlt, hwo⟩ := Array.getElem?_eq_some_iff.1 hw
  have hwp : w < places.size := by rw [z1]; exact hwlt
  have hplace : places[w] = (t, p) := by
    have e := z2 w hwlt
    rw [hwo, hpl, Array.getElem?_eq_getElem hwp] at e
    exact (Option.some.inj e).symm
  -- the tree is among those opened
  have hmem : t ∈ cols.map (·.1) := by
    rw [h3, Fmt.listOf_mem]
    simp only [Array.toList_map, List.mem_map, Array.mem_toList_iff]
    exact ⟨places[w], Array.getElem_mem hwp, by rw [hplace]⟩
  obtain ⟨m0, hm0, em0⟩ := List.mem_map.1 hmem
  obtain ⟨mine, hfind⟩ : ∃ mine, cols.find? (·.1 == t) = some mine := by
    cases hc : cols.find? (·.1 == t) with
    | some mine => exact ⟨mine, rfl⟩
    | none =>
      have := List.find?_eq_none.1 hc m0 hm0
      rw [em0] at this
      simp at this
  have hmine : mine ∈ cols := List.mem_of_find?_eq_some hfind
  have emine : mine.1 = t := by
    have := List.find?_some hfind
    simpa using this
  obtain ⟨T', k1, _, k3, k4⟩ := h4 mine hmine
  rw [emine, hT] at k1
  obtain rfl : T = T' := Option.some.inj k1
  -- the tree's columns are values of g t
  have hkey : Blk.treeKey a.book a.ch.firstTree mine.1 = T.number - a.ch.firstTree := by
    unfold Blk.treeKey
    rw [emine, hT]
    rfl
  have htm : t ∈ ts := emine ▸ hmts mine hmine
  obtain ⟨b1, b2⟩ := hbk t htm T hT
  have hs := hseg mine hmine
  rw [hkey, emine, ← b1, ← b2, ← ownList_eq, ← k3] at hs
  obtain ⟨_, hval⟩ := seg_cut (T.number - a.ch.firstTree) mine.2.1 mine.2.2 (g t) _ [] [] k4
    (List.append_nil _).symm (by rw [List.append_nil]; exact hs)
    (by rw [k3, ownList_eq, b2]; exact hin t htm)
  -- the message's symbols
  obtain ⟨w1, w2⟩ := array_mapM_inv _ _ _ h5
  have hzs : (ids.zip places).size = ids.size := by rw [Array.size_zip, z1, Nat.min_self]
  have q1 := w2 w (by rw [hzs]; exact hwlt)
  have hop' : w < out.size := by rw [w1, hzs]; exact hwlt
  rw [Array.getElem_zip, Array.getElem?_eq_getElem hop', hwo, hplace] at q1
  obtain ⟨here, c, e1, e2, e3⟩ :=
    symbolsOf_at a.st a.book pos cols o t p T x out[w] mine hT hx hfind q1 i hi
  have eo : out.getD w #[] = out[w] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hop']
    rfl
  refine ⟨c, ?_, by unfold colB; rw [eo]; exact e3⟩
  obtain ⟨hlt2, _⟩ := Array.getElem?_eq_some_iff.1 e2
  have hlt1 : here < mine.2.1.size := by rw [← k4]; exact hlt2
  have hv := hval here hlt1
  have ecd : mine.2.2.getD here #[] = c := by
    rw [Array.getD_eq_getD_getElem?, e2]
    rfl
  rw [ecd] at hv
  -- the column's position
  have hposn : mine.2.1.getD here 0 = placeIn T.shape.logN pos.logN (pos.all.getD i 0) := by
    unfold placeIn
    by_cases hl : T.shape.logN = pos.logN
    · rw [if_pos hl]
      rw [if_pos (by rw [hl]; exact beq_self_eq_true _)] at e1
      obtain rfl : i = here := Option.some.inj e1
      rw [k3]
      unfold Blk.ownList
      rw [if_pos (by rw [hl]; exact beq_self_eq_true _)]
    · rw [if_neg hl]
      rw [if_neg (by simpa using hl)] at e1
      exact (idxOf_some _ _ _ e1).2
  rw [← hposn]
  exact hv

end OnBytes.Slice.ProxRun
