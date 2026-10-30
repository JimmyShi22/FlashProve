-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/FaithFile.lean: the pieces from which `FaithAll`
(Honest/Law/Rule/ChainModel.lean) follows at each of a description's three chains (`faithAll_of` is
applied in `chain_file`, Honest/Law/Rule/ChainFile.lean, and the three chains are put together in
`model`, Honest/Law/Rule/Model.lean); and that what reads show of a tree is that tree's table's
columns at the positions read of it. No coin, no part and no run of a protocol occurs here.

  1  `faithAll_of`   one chain, under a hypothesis on the table behind a source (`htr`) and three
     more: what has been produced is `laidOf` of the three chains' rounds; as many challenges as
     rounds; each read is among the description's
  2  `own_tab`, `third_tab`   the table behind a source of `treeOwn` and of `treeThird`
  3  `allTabs_append`, `tabs_prefix`, `allTabs_length`, `allTabs_at`   the tables of a stretch from
     the start are those of the whole list; a round's tables among the chain's
  4  `filterMap_map`, `cols_by`   what reads show of a tree

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.Rule.Words
import Johnson.Desc.ProofFile.Honest.Law.Rule.ChainModel
import Johnson.Desc.ProofFile.Honest.Law.Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block FileDescription Place OpenedColumn)

variable {Xi S Cl : Type}

/-! ## 1 One chain -/

/-- **`FaithAll` at one chain.** `trip`: the three chains' rounds, as a function of this chain's. -/
theorem faithAll_of (F : FileDescription Xi) (ρ : Draws) (ch ft : Nat) (L : Lay) (Z₀ : Laid)
    (trip : List Played → List Played × List Played × List Played)
    (hZ : ∀ l, Z₀.add ch (pairsBy (treeAsks F ρ ch) l 0) =
      laidOf F ρ (trip l).1 (trip l).2.1 (trip l).2.2)
    (htr : ∀ l o pT, L.tree l o = some pT → (srcOf ch o).1 ≤ 2 ∧
      ((allTabs (pick3 (trip l).1 (trip l).2.1 (trip l).2.2
        (srcOf ch o).1))[(srcOf ch o).2]?).join = some pT.2) :
    ∀ (bs : List (Block S Cl)) (ds : List Fmt.Drawn), ds.length = (bs.map (·.rounds.length)).sum →
    (∀ q ∈ readsOf ch ft (fun _ _ => none) (fun _ => none) (bs.flatMap (·.rounds)) ds,
      q ∈ allBare F ρ) →
    FaithAll ch ft (storedShown L.stored (storedAsks F ρ)) (treeAsks F ρ ch) L Z₀ bs ds
  | [], _, _, _ => trivial
  | b :: bs, ds, hl, hm => by
    simp only [List.map_cons, List.sum_cons] at hl
    have htl : b.rounds.length = (ds.take b.rounds.length).length := by
      rw [List.length_take]
      omega
    have hsplit : readsOf ch ft (fun _ _ => none) (fun _ => none)
        ((b :: bs).flatMap (·.rounds)) ds =
        readsOf ch ft (fun _ _ => none) (fun _ => none) b.rounds (ds.take b.rounds.length) ++
          readsOf ch ft (fun _ _ => none) (fun _ => none) (bs.flatMap (·.rounds))
            (ds.drop b.rounds.length) := by
      rw [List.flatMap_cons]
      conv_lhs => rw [← List.take_append_drop b.rounds.length ds]
      exact readsOf_append _ _ _ _ _ _ _ _ htl
    rw [hsplit] at hm
    rw [FaithAll]
    refine ⟨fun l q hq w hw => ?_, faithAll_of F ρ ch ft L Z₀ trip hZ htr bs _
      (by rw [List.length_drop]; omega) fun q hq => hm q (List.mem_append.2 (Or.inr hq))⟩
    rw [hZ l]
    refine faith_one F ρ _ _ _ L.stored ch ft (L.tree l) b.rounds _ (htr l) q hq
      (hm _ (List.mem_append.2 (Or.inl ?_))) w hw
    rw [← readsOf_bare ch ft L.stored (L.tree l)]
    exact List.mem_map.2 ⟨q, hq, rfl⟩

/-! ## 2 The table behind a source -/

theorem own_tab (l : List Played) (o : Fmt.TreeSource) (pT : Place × Table)
    (h : treeOwn l o = some pT) : ∃ n, o = .own n ∧ ((allTabs l)[n]?).join = some pT.2 := by
  cases o with
  | taken c k => cases h
  | own n =>
    refine ⟨n, rfl, ?_⟩
    have h' : ((tablesOf l)[n]?).bind id = some pT := h
    rw [← tables_tabs, h']
    rfl

theorem third_tab (l₁ l₂ l₃ : List Played) (o : Fmt.TreeSource) (pT : Place × Table)
    (h : treeThird l₁ l₂ l₃ o = some pT) : (srcOf 2 o).1 ≤ 2 ∧
      ((allTabs (pick3 l₁ l₂ l₃ (srcOf 2 o).1))[(srcOf 2 o).2]?).join = some pT.2 := by
  cases o with
  | own n =>
    have h' : ((tablesOf l₃)[n]?).bind id = some pT := h
    refine ⟨Nat.le_refl 2, ?_⟩
    show ((allTabs l₃)[n]?).join = some pT.2
    rw [← tables_tabs, h']
    rfl
  | taken c k =>
    have h' : (if c == 0 then ((tablesOf l₁)[k]?).bind id
      else if c == 1 then ((tablesOf l₂)[k]?).bind id else none) = some pT := h
    by_cases h0 : c = 0
    · subst h0
      have h'' : ((tablesOf l₁)[k]?).bind id = some pT := h'
      refine ⟨(show (0 : Nat) ≤ 2 by decide), ?_⟩
      show ((allTabs l₁)[k]?).join = some pT.2
      rw [← tables_tabs, h'']
      rfl
    · by_cases h1 : c = 1
      · subst h1
        have h'' : ((tablesOf l₂)[k]?).bind id = some pT := h'
        refine ⟨(show (1 : Nat) ≤ 2 by decide), ?_⟩
        show ((allTabs l₂)[k]?).join = some pT.2
        rw [← tables_tabs, h'']
        rfl
      · rw [if_neg (by simpa using h0), if_neg (by simpa using h1)] at h'
        cases h'

/-! ## 3 Tables by their numbers -/

theorem allTabs_append (l₁ l₂ : List Played) : allTabs (l₁ ++ l₂) = allTabs l₁ ++ allTabs l₂ := by
  unfold allTabs
  rw [List.flatMap_append]

/-- A table of a stretch from the start is the table of that number of the whole list. -/
theorem tabs_prefix (l₁ l₂ : List Played) (j : Nat) (T : Table)
    (h : ((allTabs l₁)[j]?).join = some T) : ((allTabs (l₁ ++ l₂))[j]?).join = some T := by
  have hj : j < (allTabs l₁).length := by
    by_contra hn
    rw [List.getElem?_eq_none_iff.2 (Nat.le_of_not_lt hn)] at h
    cases h
  rw [allTabs_append, List.getElem?_append_left hj]
  exact h

theorem allTabs_length (l : List Played) :
    (allTabs l).length = (l.map (·.tables.length)).sum := by
  unfold allTabs
  rw [List.length_flatMap]

/-- A round's tables among the chain's. -/
theorem allTabs_at (l₁ : List Played) (p : Played) (l₂ : List Played) (i : Nat)
    (hi : i < p.tables.length) :
    (allTabs (l₁ ++ p :: l₂))[(l₁.map (·.tables.length)).sum + i]? = p.tables[i]? := by
  rw [allTabs_append, List.getElem?_append_right (by rw [allTabs_length]; omega), allTabs_length,
    Nat.add_sub_cancel_left]
  show (p.tables ++ allTabs l₂)[i]? = _
  rw [List.getElem?_append_left hi]

/-! ## 4 What reads show of a tree -/

theorem filterMap_map {α β : Type} (f : α → Option β) (g : α → β) : ∀ l : List α,
    (∀ a ∈ l, f a = some (g a)) → l.filterMap f = l.map g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.filterMap_cons, h a (List.mem_cons.2 (Or.inl rfl)),
      filterMap_map f g l fun b hb => h b (List.mem_cons_of_mem _ hb)]
    rfl

/-- **What reads show of a tree is its table's columns at the positions read of it.** `qs`: reads
whose keys, positions and sources are the description's at these challenges. `T`: the tree's table,
if one is available. -/
theorem cols_by (F : FileDescription Xi) (ρ : Draws) (qs : List Read) (hb : qs.map Read.bare = allBare F ρ)
    (c j : Nat) (T : Option Table)
    (hq : ∀ q ∈ qs, q.src = some (c, j) → q.words.isSome = true ∧
      q.words = T.map (·.col q.pos)) :
    colsBy c qs j = colsOfT T (treeAsks F ρ c j) := by
  have ht : treeAsks F ρ c j = (qs.filter fun q => q.src == some (c, j)).map (·.pos) := by
    unfold treeAsks
    rw [← hb, pos_bare]
  have hf : ∀ q ∈ qs.filter fun q => q.src == some (c, j), q.words.isSome = true ∧
      q.words = T.map (·.col q.pos) := by
    intro q hq'
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hq'
    exact hq q h1 (beq_iff_eq.1 h2)
  unfold colsBy
  rw [ht]
  cases T with
  | none =>
    have he : (qs.filter fun q => q.src == some (c, j)) = [] := by
      cases hl : qs.filter fun q => q.src == some (c, j) with
      | nil => rfl
      | cons a l =>
        obtain ⟨h1, h2⟩ := hf a (by rw [hl]; exact List.mem_cons.2 (Or.inl rfl))
        rw [h2] at h1
        cases h1
    rw [he]
    rfl
  | some T =>
    rw [filterMap_map _ (fun q => (q.pos, T.col q.pos)) _ fun q hq' => by
      rw [(hf q hq').2]
      rfl]
    show _ = ((qs.filter fun q => q.src == some (c, j)).map (·.pos)).map fun x => (x, T.col x)
    rw [List.map_map]
    rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.faithAll_of
#print axioms ProofFile.Honest.own_tab
#print axioms ProofFile.Honest.third_tab
#print axioms ProofFile.Honest.allTabs_append
#print axioms ProofFile.Honest.tabs_prefix
#print axioms ProofFile.Honest.allTabs_length
#print axioms ProofFile.Honest.allTabs_at
#print axioms ProofFile.Honest.filterMap_map
#print axioms ProofFile.Honest.cols_by
