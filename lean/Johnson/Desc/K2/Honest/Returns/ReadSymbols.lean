-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/ReadSymbols.lean: AN ORACLE MESSAGE's SYMBOLS ARE FOUND IN THE OPENED
COLUMNS (`symbolsAt`, Johnson/Desc/Own/Symbols.lean) wherever its tree was opened at its own list
with as many columns; there is one column a position, with as many main and mask symbols as the
message has rows. Statements and proofs.

  `ofDraws_all`     of the positions that a round's draws make, every listed one is among the draws
  `where_found`     each listed position is found in a tree's own list: at its own number where the
                    tree is as long as the positions' range; else modulo the tree's length
  `columnOf_sizes`  a column has as many symbols as the message has rows
  `symbolsAt_returns`   the whole

Limits. That every listed position is among the draws is a premise (`ofDraws_all`: it holds of the
positions that a round's draws make). Nothing on the symbols' values. Nothing on any property.

-/
import Johnson.Desc.Own.Symbols
import Johnson.Top.H0.Tw.K2.RowsCanMeans
import Johnson.Top.H0.Tw.K2.RowsMadeAgree
import OnBytes.Slice.BlkProxMany

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc.Own (symbolsAt whereOpened Opened)

/-- Of the positions that a round's draws make, every listed one is among the draws. -/
theorem ofDraws_all (logN : Nat) (draws : List Nat) :
    ∀ x ∈ (Positions.ofDraws logN draws).all.toList,
      x ∈ (Positions.ofDraws logN draws).draws.toList := by
  intro x hx
  have hx' : x ∈ listOfT draws := hx
  rw [listOfT_eq] at hx'
  exact (Fmt.listOf_mem draws x).1 hx'

/-- Each listed position is found in a tree's own list. -/
theorem where_found (tree : Tree) (pos : Positions)
    (hall : ∀ x ∈ pos.all.toList, x ∈ pos.draws.toList) {i : Nat} (hi : i < pos.all.size) :
    ∃ here, whereOpened (tree.shape.logN == pos.logN) (Blk.ownList tree pos)
        (2 ^ tree.shape.logN) i (pos.all.getD i 0) = some here ∧
      here < (Blk.ownList tree pos).size := by
  unfold whereOpened
  by_cases h : (tree.shape.logN == pos.logN) = true
  · rw [if_pos h]
    refine ⟨i, rfl, ?_⟩
    unfold Blk.ownList
    rw [if_pos h]
    exact hi
  · rw [if_neg h]
    have hg : pos.all.getD i 0 ∈ pos.all.toList := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi, Option.getD_some]
      exact Array.getElem_mem_toList hi
    have hm : pos.all.getD i 0 % 2 ^ tree.shape.logN ∈ Blk.ownList tree pos := by
      unfold Blk.ownList
      rw [if_neg h, List.mem_toArray, listOfT_eq]
      refine (Fmt.listOf_mem _ _).2 ?_
      rw [Array.toList_map]
      exact List.mem_map.2 ⟨_, hall _ hg, rfl⟩
    obtain ⟨here, hh⟩ := Option.isSome_iff_exists.1 ((_root_.Tw.K2.idxSome _ _).2 hm)
    exact ⟨here, hh, (OnBytes.Slice.ProxRun.idxOf_some _ _ _ hh).1⟩

/-- A column has as many symbols as the message has rows. -/
theorem columnOf_sizes (x : Oracle) (a b : Nat) (c : Array F) :
    (Blk.columnOf x a b c).main.size = x.shape.mainRows ∧
      (Blk.columnOf x a b c).mask.size = x.shape.maskRows := by
  unfold Blk.columnOf
  exact ⟨by simp, by simp⟩

/-- **The message's symbols are found.** -/
theorem symbolsAt_returns {S : Statement} {B : TreeBook} {pos : Positions} {cols : List Opened}
    {o : Nat} {p : Nat × Nat} {tree : Tree} {x : Oracle} {cs : Array (Array F)}
    (ht : B.trees[p.1]? = some tree) (hx : S.oracles[o]? = some x)
    (hf : cols.find? (·.1 == p.1) = some (p.1, Blk.ownList tree pos, cs))
    (hz : cs.size = (Blk.ownList tree pos).size)
    (hall : ∀ x ∈ pos.all.toList, x ∈ pos.draws.toList) :
    ∃ out, symbolsAt S B pos cols o p = some out ∧ ∀ i < pos.all.size, ∃ c,
      out[i]? = some c ∧ c.main.size = x.shape.mainRows ∧ c.mask.size = x.shape.maskRows := by
  let a := (tree.shape.mainSymbols.extract 0 p.2).foldl (· + ·) 0
  let b := tree.shape.mainWidth + (tree.shape.maskSymbols.extract 0 p.2).foldl (· + ·) 0
  let f : Nat → Option Column := fun i =>
    (whereOpened (tree.shape.logN == pos.logN) (Blk.ownList tree pos) (2 ^ tree.shape.logN) i
        (pos.all.getD i 0)).bind fun here => (cs[here]?).map (Blk.columnOf x a b)
  have e : symbolsAt S B pos cols o p = ((List.range pos.all.size).mapM f).map List.toArray := by
    unfold symbolsAt
    rw [ht, hx, hf]
  have hfi : ∀ i < pos.all.size, ∃ col, f i = some (Blk.columnOf x a b col) := by
    intro i hi
    obtain ⟨here, h1, h2⟩ := where_found tree pos hall hi
    refine ⟨cs[here]'(hz ▸ h2), ?_⟩
    show (whereOpened _ _ _ _ _).bind _ = _
    rw [h1]
    show (cs[here]?).map _ = _
    rw [Array.getElem?_eq_getElem (hz ▸ h2)]
    rfl
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (_root_.Tw.K2.mapM_some f (List.range pos.all.size)
    fun i hi => by
      obtain ⟨col, hc⟩ := hfi i (List.mem_range.1 hi)
      rw [hc]
      rfl)
  obtain ⟨k1, k2⟩ := OnBytes.Slice.list_mapM_inv f _ r hr
  refine ⟨r.toArray, by rw [e, hr]; rfl, fun i hi => ?_⟩
  obtain ⟨col, hc⟩ := hfi i hi
  have hi' : i < (List.range pos.all.size).length := by rw [List.length_range]; exact hi
  have h3 := k2 i hi'
  rw [List.getElem_range, hc] at h3
  refine ⟨Blk.columnOf x a b col, ?_, (columnOf_sizes x a b col).1, (columnOf_sizes x a b col).2⟩
  rw [List.getElem?_toArray]
  exact h3.symm

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.symbolsAt_returns
#print axioms VerifiableInference.Desc.K2.Honest.Returns.ofDraws_all
