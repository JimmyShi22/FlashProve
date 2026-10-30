-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/ShapeIsTold.lean: code switching (the kind K2): «TOLD IS LAID» FOR THE
KIND's SENDINGS: what the kind's sub-protocol tells of a tree (P1K2.oraclesAt,
Johnson/Desc/ProofFile/Lot/K2OfPlan.lean) has the shape that the program's pure layTrees lays for
that tree: K12's ShapeIs (Johnson/Desc/K12/Coin/FramesTie.lean). On the list of notices alone: no
state, no file. NO BLOCK IMPORTS THIS FILE.
  fill_mask        an invariant of layTrees' filling loop, from trees without symbols: in every
                   tree as many mask symbols as main symbols (each step pushes one of each)
  lay_mask         so in every tree that layTrees returns
  part_there       every part j of every tree i has its notice: the search in oraclesAt's text
                   answers
  filterMap_maps   a filterMap that answers everywhere, read through a projection, is a map
  shapeIs_told     layTrees codes sent = some lay · 0 < sent.size · lay.shapes[i]? = some T ·
                   (oraclesAt grp codes sent)[i]? = some u ⟹ ShapeIs T u: part by part the main |
                   mask symbols are the tenants' main | mask words; the depth is the log-length
WHAT IT DOES NOT SAY. That a tree of the whole chain's lay (K12.Door.laidAtCodes) is this
sending's, or that the description's oracle at a number is this sending's told one. BY:
P1K2.lay_facts · cnt_hit · layTrees_shapes (Tw/K2C/ToldTenants.lean) · fill_cnt |
layTrees_fits (Johnson/Desc/Book/BookFits.lean). No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.ToldTenants
import Johnson.Desc.K12.Coin.FramesTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open OnBytes
open OnBytes.Params (laidOf)
open OnBytes.Tie.Pv.Keeps.Fit (fillStep Blank laid_spec getD_modify getD_modify_ne)
open VerifiableInference.Desc.Book (cnt fill_cnt layTrees_fits LayFits)
open VerifiableInference.Desc.K12.Coin (ShapeIs)

theorem fill_mask (codes : Codes) (sent : Array OracleNotice) (A0 : Array TreeShape)
    (w0 tree : Array Nat) (hB : Blank A0) (hr : ∀ j, j < sent.size → tree.getD j 0 < A0.size) :
    ∀ (k : Nat) (s : Array TreeShape × Array Nat × Array Nat), k ≤ sent.size →
      (List.range k).foldlM (fillStep codes sent tree) (A0, #[], w0) = some s →
      ∀ τ, (s.1.getD τ {}).maskSymbols.size = (s.1.getD τ {}).mainSymbols.size
  | 0, s, _, h => by
    obtain rfl : (A0, #[], w0) = s := Option.some.inj h
    intro τ
    show (A0.getD τ {}).maskSymbols.size = (A0.getD τ {}).mainSymbols.size
    rw [(hB τ).2.1, (hB τ).2.2]
  | k + 1, s, hk, h => by
    rw [List.range_succ, List.foldlM_append] at h
    obtain ⟨s0, h0, h1⟩ := Option.bind_eq_some_iff.1 h
    have ih := fill_mask codes sent A0 w0 tree hB hr k s0 (Nat.le_of_succ_le hk) h0
    obtain ⟨sz, _, _, _⟩ := fill_cnt codes sent A0 w0 tree hB hr k s0 (Nat.le_of_succ_le hk) h0
    have h1' : fillStep codes sent tree s0 k = some s := by
      rw [List.foldlM_cons] at h1
      obtain ⟨y1, a1, a2⟩ := Option.bind_eq_some_iff.1 h1
      obtain rfl : y1 = s := Option.some.inj a2
      exact a1
    have hτ : tree.getD k 0 < A0.size := hr k hk
    unfold fillStep at h1'
    dsimp only at h1'
    split at h1'
    · cases h1'
    · obtain rfl := Option.some.inj h1'
      intro τ
      by_cases e : tree.getD k 0 = τ
      · subst e
        rw [getD_modify _ _ _ _ (by rw [sz]; exact hτ)]
        show (Array.push _ _).size = (Array.push _ _).size
        rw [Array.size_push, Array.size_push, ih]
      · rw [getD_modify_ne _ _ _ _ _ e]
        exact ih τ

theorem lay_mask {codes : Codes} {sent : Array OracleNotice} {T : TreeLay}
    (h : layTrees codes sent = some T) (h0 : 0 < sent.size) :
    ∀ τ, τ < T.shapes.size →
      (T.shapes.getD τ {}).maskSymbols.size = (T.shapes.getD τ {}).mainSymbols.size := by
  obtain ⟨filled, hf, _, _, eS⟩ := layTrees_shapes h
  have hB : Blank (laidOf codes sent).1 := (laid_spec (codes := codes) h0).1.1
  have hr : ∀ j, j < sent.size → (laidOf codes sent).2.2.getD j 0 < (laidOf codes sent).1.size :=
    fun j hj => (laid_spec (codes := codes) hj).2.1
  have hm := fill_mask codes sent _ _ _ hB hr sent.size filled (Nat.le_refl _) hf
  intro τ hτ
  have hτ' : τ < filled.1.size := by
    rw [eS, Array.size_map] at hτ
    exact hτ
  have e := hm τ
  rw [eS]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hτ']
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hτ'] at e
  show (if _ then _ else _ : TreeShape).maskSymbols.size =
    (if _ then _ else _ : TreeShape).mainSymbols.size
  split <;> exact e

theorem part_there {codes : Codes} {sent : Array OracleNotice} {lay : TreeLay}
    (h : layTrees codes sent = some lay) (h0 : 0 < sent.size) {i : Nat}
    (hi : i < lay.shapes.size) {j : Nat} (hj : j < (lay.shapes.getD i {}).mainSymbols.size) :
    ((List.range sent.size).find? fun n =>
      lay.tree.getD n noId == i && lay.part.getD n noId == j).isSome = true := by
  obtain ⟨zt, zp, hs⟩ := lay_facts h h0
  have hF : LayFits sent.size lay := layTrees_fits h
  rw [hs i hi] at hj
  obtain ⟨n, hn, e1, e2⟩ := cnt_hit lay.tree i sent.size j hj
  rw [List.find?_isSome]
  refine ⟨n, List.mem_range.2 hn, ?_⟩
  have g1 : lay.tree.getD n noId = lay.tree.getD n 0 := by
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by rw [zt]; exact hn)]
    rfl
  have g2 : lay.part.getD n noId = lay.part.getD n 0 := by
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by rw [zp]; exact hn)]
    rfl
  rw [g1, g2, e1, (hF n hn).2, e1, e2]
  simp

theorem filterMap_maps {α β γ : Type} (f : α → Option β) (π : β → γ) (ρ : α → γ) :
    ∀ l : List α, (∀ x ∈ l, ∃ y, f x = some y ∧ π y = ρ x) → (l.filterMap f).map π = l.map ρ
  | [], _ => rfl
  | x :: l, h => by
    obtain ⟨y, hy, e⟩ := h x (by simp)
    rw [List.filterMap_cons_some hy, List.map_cons, List.map_cons, e,
      filterMap_maps f π ρ l fun z hz => h z (by simp [hz])]

theorem toList_getD (a : Array Nat) (n : Nat) (hn : n = a.size) :
    a.toList = (List.range n).map fun j => a.getD j 0 := by
  subst hn
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [Array.getElem_toList, List.getElem_map, List.getElem_range]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using h1)]
    rfl

theorem shapeIs_told {grp : Nat} {codes : Codes} {sent : Array OracleNotice} {lay : TreeLay}
    (h : layTrees codes sent = some lay) (h0 : 0 < sent.size) {i : Nat} {T : TreeShape}
    {u : VerifiableInference.Desc.Oracle} (hT : lay.shapes[i]? = some T)
    (hu : (oraclesAt grp codes sent)[i]? = some u) : ShapeIs T u := by
  have hi : i < lay.shapes.size := (Array.getElem?_eq_some_iff.1 hT).1
  have hTd : lay.shapes.getD i {} = T := by
    rw [Array.getD_eq_getD_getElem?, hT]
    rfl
  unfold oraclesAt at hu
  rw [h] at hu
  simp only [List.getElem?_map, List.getElem?_zipIdx, Array.getElem?_toList, hT, Option.map_some,
    Nat.zero_add] at hu
  obtain rfl := Option.some.inj hu
  have hit : ∀ j ∈ List.range T.mainSymbols.size,
      ((List.range sent.size).find? fun n =>
        lay.tree.getD n noId == i && lay.part.getD n noId == j).isSome = true := by
    intro j hj
    exact part_there h h0 hi (by rw [hTd]; exact List.mem_range.1 hj)
  have hmk : T.maskSymbols.size = T.mainSymbols.size := by
    have := lay_mask h h0 i hi
    rw [hTd] at this
    exact this
  refine ⟨?_, ?_, rfl⟩
  · rw [toList_getD T.mainSymbols _ rfl]
    refine (filterMap_maps _ _ _ _ fun j hj => ?_).symm
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 (hit j hj)
    exact ⟨_, by rw [hn]; rfl, rfl⟩
  · rw [toList_getD T.maskSymbols _ hmk.symm]
    refine (filterMap_maps _ _ _ _ fun j hj => ?_).symm
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 (hit j hj)
    exact ⟨_, by rw [hn]; rfl, rfl⟩

end P1K2

#print axioms P1K2.fill_mask
#print axioms P1K2.lay_mask
#print axioms P1K2.part_there
#print axioms P1K2.shapeIs_told
