-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/Kpw.lean: WHAT THE TEST "THE COLUMNS" OF `Block.step` SAYS OF A DEALT GROUP.
Statements and proofs, for rounds that open no stored table.

  `regroup_mem`: under that test every column of dealt group number i is a column of the view whose
    key, position and width stand in the declared group number i.
  `groupsOf_key`: all of declared group number i stands under the key, at the width and inside the
    depth of the rounds' opening number i.
  `dealt_wide`: so every column of dealt group number i is as wide as opening number i declares, at
    a position inside its declared depth.
A tool.
-/
import Johnson.Desc.K12.Law.ViewWide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc
open H2K.Sw (kpw)

theorem regroup_mem : ∀ (groups : List (List H2K.Sw.Want)) (got : List OpenedColumn),
    got.map kpw = groups.flatMap id → ∀ (i : ℕ) (grp : List (ℕ × List UInt64)),
    (regroup (groups.map (·.length)) got)[i]? = some grp →
    ∃ g, groups[i]? = some g ∧ ∀ z ∈ grp, ∃ o ∈ got, (o.2.1, o.2.2) = z ∧ kpw o ∈ g
  | [], _, _, _, _, hi => by cases hi
  | g :: gs, got, h, i, grp, hi => by
    rw [List.flatMap_cons] at h
    have h1 : (got.take g.length).map kpw = g := by
      rw [List.map_take, h]
      exact List.take_left' rfl
    have h2 : (got.drop g.length).map kpw = gs.flatMap id := by
      rw [List.map_drop, h]
      exact List.drop_left' rfl
    have e : regroup ((g :: gs).map (·.length)) got =
        ((got.take g.length).map fun c => (c.2.1, c.2.2)) ::
          regroup (gs.map (·.length)) (got.drop g.length) := rfl
    rw [e] at hi
    cases i with
    | zero =>
      obtain rfl := Option.some.inj hi
      refine ⟨g, rfl, fun z hz => ?_⟩
      obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hz
      refine ⟨o, List.mem_of_mem_take ho, rfl, ?_⟩
      have := List.mem_map_of_mem (f := kpw) ho
      rwa [h1] at this
    | succ i =>
      obtain ⟨g', hg', H⟩ := regroup_mem gs (got.drop g.length) h2 i grp hi
      refine ⟨g', hg', fun z hz => ?_⟩
      obtain ⟨o, ho, h3, h4⟩ := H z hz
      exact ⟨o, List.mem_of_mem_drop ho, h3, h4⟩

theorem groupsOf_key (ft : ℕ) : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    (∀ d ∈ ds, d.stored = []) → ∀ (i : ℕ) (g : List H2K.Sw.Want), (groupsOf ft ds Rs)[i]? = some g →
    ∃ o, (ds.flatMap (·.opens))[i]? = some o ∧
      ∀ w ∈ g, w.1 = o.1.tree - ft ∧ w.2.2 = o.1.W ∧ w.2.1 < 2 ^ o.1.a
  | [], _, _, _, _, hi => by simp [groupsOf] at hi
  | _ :: _, [], _, _, _, hi => by simp [groupsOf] at hi
  | d :: ds, R :: Rs, hs, i, g, hi => by
    simp only [groupsOf, hs d (List.mem_cons_self ..), List.map_nil, List.nil_append] at hi
    rw [List.flatMap_cons]
    by_cases hlt : i < d.opens.length
    · rw [List.getElem?_append_left (by rw [List.length_map]; exact hlt), List.getElem?_map] at hi
      rw [List.getElem?_append_left hlt]
      obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hi
      refine ⟨o, ho, fun w hw => ?_⟩
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hw
      exact ⟨rfl, rfl, H2K.First.listOf_lt _ _ _ (Nat.pow_pos (by decide)) hx⟩
    · rw [List.getElem?_append_right (by rw [List.length_map]; omega), List.length_map] at hi
      rw [List.getElem?_append_right (by omega)]
      exact groupsOf_key ft ds Rs (fun d hd => hs d (List.mem_cons_of_mem _ hd)) _ g hi

theorem dealt_wide (ft : ℕ) (ds : List Fmt.DeclaredRound) (hd : ∀ d ∈ ds, d.stored = [])
    (Rs : List Fmt.Drawn) (got : List OpenedColumn) (hcols : got.map kpw = (groupsOf ft ds Rs).flatMap id)
    (i : ℕ) (grp : List (ℕ × List UInt64))
    (hi : (regroup ((groupsOf ft ds Rs).map (·.length)) got)[i]? = some grp) :
    ∃ o, (ds.flatMap (·.opens))[i]? = some o ∧
      ∀ z ∈ grp, z.2.length = o.1.W ∧ z.1 < 2 ^ o.1.a := by
  obtain ⟨g, hg, H⟩ := regroup_mem _ _ hcols i grp hi
  obtain ⟨o, ho, K⟩ := groupsOf_key ft ds Rs hd i g hg
  refine ⟨o, ho, fun z hz => ?_⟩
  obtain ⟨c, _, rfl, hk⟩ := H z hz
  exact ⟨(K _ hk).2.1, (K _ hk).2.2⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.dealt_wide
