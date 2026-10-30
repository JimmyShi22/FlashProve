-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/ToldOfLay.lean: **WHAT A SENDING BLOCK TELLS OF ITS TREES IS THE LAYOUT's OWN
SHAPES AND PARTS**, on the plan alone. Statements and proofs.

A sending block of the linear claim's chain tells of each of its trees an `Oracle`
(`Desc.K14.oraclesOf codes sent gs`, Johnson/Desc/K14/Blocks.lean): off the layout that
`Own.treesMade codes sent` gives. The record's book is meant to get its trees' shapes and its
messages' parts from the same layout (not shown here). FramesTie.lean asks that the two agree
(`ShapeIs`; "the part is the tenant").
Let Own.treesMade codes sent = some lay, and gs as long as sent.
  `told_at`: the entry number τ of what is told, written out.
  `told_shape`: of each tree τ of lay: something is told of it, and `ShapeIs` holds of lay's shape
    and what is told.
  `told_tenant`: message i is the tenant number lay.part i of what is told of its tree: with its
    main rows times their degree and its mask rows times 3 for words.
By LaySymbols.lean's two laws on `layTrees` and `treesMade_eq` (Johnson/Desc/Own/TreesAgree.lean).
Limits. Nothing on soundness. ON ONE SENDING's OWN LIST: that a description's `oracleAt` at a tree's
number through the file is this list's entry is of the description's blocksInOrder lists: not said here. That
a record's book holds lay's shapes and parts is of the receiving: not said here.

-/
import Johnson.Desc.K12.Coin.LaySymbols
import Johnson.Desc.K12.Coin.FramesTie
import Johnson.Desc.K14.Blocks
import Johnson.Desc.Own.TreesAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.LayTreesLaws
open VerifiableInference.Desc

/-- A list with its places, off the numbers below its length. -/
theorem zipIdx_range {α : Type} (l : List α) (d : α) :
    l.zipIdx = (List.range l.length).map fun i => (l.getD i d, i) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp at h1
    simp [List.getD_eq_getElem?_getD, h1]

/-- One tenant, as the sending block's text makes it. -/
def tenantOf (sent : Array OracleNotice) (gs : List (List Nat)) (i : Nat) : SymbolComponent :=
  { main := mainW sent i, mask := maskW sent i, degree := (sent.getD i default).shape.mainDeg
    sampled := (sent.getD i default).shape.answers != 0, groups := gs.getD i [] }

section
variable (codes : Codes) (sent : Array OracleNotice) (gs : List (List Nat)) (lay : TreeLay)

/-- **The entry number τ of what is told.** -/
theorem told_at (h : Own.treesMade codes sent = some lay) (hg : gs.length = sent.size) (τ : Nat)
    (T : TreeShape) (hT : lay.shapes[τ]? = some T) :
    (_root_.Desc.K14.oraclesOf codes sent gs)[τ]? = some
      { logLength := T.logN, words := T.mainWidth + T.maskWidth
        tenants := (inTree lay.tree τ sent.size).map (tenantOf sent gs) } := by
  have hl : layTrees codes sent = some lay := by rw [← Own.treesMade_eq]; exact h
  have hsz := layTrees_treeSize codes sent lay hl
  unfold _root_.Desc.K14.oraclesOf
  rw [h]
  dsimp only
  rw [List.getElem?_map, List.getElem?_zipIdx, Array.getElem?_toList, hT]
  simp only [Option.map_some, Nat.zero_add]
  congr 2
  rw [zipIdx_range _ (default, []), List.filter_map, List.map_map]
  have hlen : (sent.toList.zip gs).length = sent.size := by
    rw [List.length_zip, Array.length_toList, hg, Nat.min_self]
  rw [hlen]
  unfold inTree
  have hf : (List.range sent.size).filter
        ((fun x : (OracleNotice × List Nat) × Nat => lay.tree[x.2]? == some τ) ∘
          fun i => ((sent.toList.zip gs).getD i (default, []), i)) =
      (List.range sent.size).filter fun i => lay.tree.getD i 0 == τ := by
    refine List.filter_congr fun i hi => ?_
    have hi' : i < lay.tree.size := by rw [hsz]; exact List.mem_range.1 hi
    show (lay.tree[i]? == some τ) = (lay.tree.getD i 0 == τ)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi']
    simp
  rw [hf]
  refine List.map_congr_left fun i hi => ?_
  have hi' : i < sent.size := List.mem_range.1 (List.mem_filter.1 hi).1
  have e : (sent.toList.zip gs).getD i (default, []) = (sent.getD i default, gs.getD i []) := by
    have h2 : i < gs.length := by rw [hg]; exact hi'
    simp [List.getD_eq_getElem?_getD, h2, hi', Array.getD_eq_getD_getElem?]
  show _ = tenantOf sent gs i
  simp only [Function.comp, e]
  rfl

/-- **Of each tree something is told, and it is the layout's shape.** -/
theorem told_shape (h : Own.treesMade codes sent = some lay) (hg : gs.length = sent.size)
    (τ : Nat) (T : TreeShape) (hT : lay.shapes[τ]? = some T) :
    ∃ o, (_root_.Desc.K14.oraclesOf codes sent gs)[τ]? = some o ∧ ShapeIs T o := by
  have hl : layTrees codes sent = some lay := by rw [← Own.treesMade_eq]; exact h
  obtain ⟨a, b⟩ := layTrees_symbols codes sent lay hl τ T hT
  refine ⟨_, told_at codes sent gs lay h hg τ T hT, ?_, ?_, rfl⟩
  · rw [a, List.map_map]
    rfl
  · rw [b, List.map_map]
    rfl

/-- **A message is the tenant that its part names.** -/
theorem told_tenant (h : Own.treesMade codes sent = some lay) (hg : gs.length = sent.size)
    (i : Nat) (hi : i < sent.size) (o : Oracle)
    (ho : (_root_.Desc.K14.oraclesOf codes sent gs)[lay.tree.getD i 0]? = some o) :
    o.tenants[lay.part.getD i 0]? = some (tenantOf sent gs i) := by
  have hl : layTrees codes sent = some lay := by rw [← Own.treesMade_eq]; exact h
  have hp := layTrees_part codes sent lay hl i hi
  have hT : ∃ T, lay.shapes[lay.tree.getD i 0]? = some T := by
    unfold _root_.Desc.K14.oraclesOf at ho
    rw [h] at ho
    dsimp only at ho
    rw [List.getElem?_map, List.getElem?_zipIdx, Array.getElem?_toList] at ho
    cases hs : lay.shapes[lay.tree.getD i 0]? with
    | none => rw [hs] at ho; cases ho
    | some T => exact ⟨T, rfl⟩
  obtain ⟨T, hT⟩ := hT
  have e := told_at codes sent gs lay h hg _ T hT
  rw [ho] at e
  have ep : lay.part.getD i 0 = (inTree lay.tree (lay.tree.getD i 0) i).length := by
    rw [Array.getD_eq_getD_getElem?, hp]
    rfl
  rw [Option.some.inj e, ep]
  show ((inTree lay.tree (lay.tree.getD i 0) sent.size).map (tenantOf sent gs))[
    (inTree lay.tree (lay.tree.getD i 0) i).length]? = _
  rw [List.getElem?_map, inTree_get lay.tree _ i rfl sent.size hi]
  rfl

end

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.told_at
#print axioms VerifiableInference.Desc.K12.Coin.told_shape
#print axioms VerifiableInference.Desc.K12.Coin.told_tenant
