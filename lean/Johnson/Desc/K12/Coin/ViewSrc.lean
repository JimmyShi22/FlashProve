-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/ViewSrc.lean: WHAT A BLOCK IS DEALT OF A STAGE's OWN VIEW, BY THE OPENING's
NUMBER: each dealt group is the columns of THE TREE THAT THE DECLARED OPENING OF THAT NUMBER NAMES
BY ITS SOURCE. Statements and proofs, for rounds that open no stored table.

A view shows a column under a key, and keys do not part the trees of a file (on a later chain a tree
that is taken over and the chain's first own tree stand under one key: Johnson/Desc/BlockSlot.lean's
head). Which tree a group is of is said by the order of the openings alone. The premise is that
file's own form (`WantsAre`): the stage's wants are the declared rounds' wants (`wantsDecl num`),
each tree by its number over the file; num: from a declared source to that number.

  `wantsDecl_flat`, `groupsOf_flat`: the declared wants and the declared groups over one flat list
    of the openings, each with its round's draws (`opensWith`, Johnson/Desc/K12/Law/StepAt.lean).
  `block_cols`: the wants of one opening, all answered, as columns.
  `dealt_flat`, `dealt_by_src`: **dealt group number i holds, at each of its positions, the column
    of the tree num o.2, o the declared opening number i.**
A tool.
-/
import OnBytes.Maker.Stage
import Johnson.Desc.BlockSlot
import Johnson.Desc.K12.Law.ViewWide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open Iop _root_.Run _root_.Run.PQ OnBytes.Maker
open VerifiableInference.Desc
open H2K.Sw (opensWith)

abbrev ToldP : Type := (Fmt.Shape × Fmt.TreeSource) × List ℕ

/-- The positions that an opening reads of its round's draws. -/
def posOf (y : ToldP) : List ℕ := Fmt.listOf (y.2.map (· % 2 ^ y.1.1.a))

theorem wantsDecl_flat (num : Fmt.TreeSource → ℕ) : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    (∀ d ∈ ds, d.stored = []) →
    wantsDecl num ds Rs = (opensWith ds Rs).flatMap fun y => (posOf y).map (Want.tree (num y.1.2))
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | d :: ds, R :: Rs, h => by
    show (d.stored.flatMap _) ++ (d.opens.flatMap _) ++ wantsDecl num ds Rs =
      (d.opens.map (fun o => (o, R.poss)) ++ opensWith ds Rs).flatMap _
    rw [h d List.mem_cons_self, List.flatMap_nil, List.nil_append, List.flatMap_append,
      List.flatMap_map, wantsDecl_flat num ds Rs fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

theorem groupsOf_flat (ft : ℕ) : ∀ (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn),
    (∀ d ∈ ds, d.stored = []) →
    groupsOf ft ds Rs =
      (opensWith ds Rs).map fun y => (posOf y).map fun x => (y.1.1.tree - ft, x, y.1.1.W)
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | d :: ds, R :: Rs, h => by
    show (d.stored.map _) ++ (d.opens.map _) ++ groupsOf ft ds Rs =
      (d.opens.map (fun o => (o, R.poss)) ++ opensWith ds Rs).map _
    rw [h d List.mem_cons_self, List.map_nil, List.nil_append, List.map_append, List.map_map,
      groupsOf_flat ft ds Rs fun x hx => h x (List.mem_cons_of_mem _ hx)]
    rfl

section
variable (C : CK) (St : StageD) (y : St.Ei.Str) (τ : Iop.Tr (uLT C St.ds))

/-- A want with its column, as the stage's view shows it. -/
def shown (w : Want) : Option OpenedColumn :=
  (sCol C St y τ w).map fun c =>
    match w with
    | .table item x => (Fmt.storedKey item, x, c)
    | .tree j x => (St.key j, x, c)

theorem block_cols (j : ℕ) : ∀ (X : List ℕ),
    (∀ x ∈ X, (sCol C St y τ (.tree j x)).isSome = true) →
    (X.map (Want.tree j)).filterMap (shown C St y τ) =
      X.map fun x => (St.key j, x, (sCol C St y τ (.tree j x)).getD [])
  | [], _ => rfl
  | x :: X, h => by
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (h x List.mem_cons_self)
    have e : shown C St y τ (.tree j x) = some (St.key j, x, c) := by
      unfold shown
      rw [hc]
      rfl
    rw [List.map_cons, List.filterMap_cons_some e, List.map_cons, hc,
      block_cols j X fun z hz => h z (List.mem_cons_of_mem _ hz)]
    rfl

theorem dealt_flat (num : Fmt.TreeSource → ℕ) (ft : ℕ) : ∀ (OW : List ToldP),
    (∀ w ∈ OW.flatMap (fun y => (posOf y).map (Want.tree (num y.1.2))),
      (sCol C St y τ w).isSome = true) →
    ∀ (i : ℕ) (grp : List (ℕ × List UInt64)),
    (regroup ((OW.map fun y => (posOf y).map fun x => (y.1.1.tree - ft, x, y.1.1.W)).map (·.length))
      ((OW.flatMap fun y => (posOf y).map (Want.tree (num y.1.2))).filterMap
        (shown C St y τ)))[i]? = some grp →
    ∃ u, OW[i]? = some u ∧ ∀ z ∈ grp, sCol C St y τ (.tree (num u.1.2) z.1) = some z.2
  | [], _, _, _, hi => by cases hi
  | u :: OW, hans, i, grp, hi => by
    have h1 : ∀ x ∈ posOf u, (sCol C St y τ (.tree (num u.1.2) x)).isSome = true := fun x hx =>
      hans _ (by
        rw [List.flatMap_cons]
        exact List.mem_append_left _ (List.mem_map_of_mem hx))
    have h2 : ∀ w ∈ OW.flatMap (fun y => (posOf y).map (Want.tree (num y.1.2))),
        (sCol C St y τ w).isSome = true := fun w hw =>
      hans _ (by
        rw [List.flatMap_cons]
        exact List.mem_append_right _ hw)
    rw [List.flatMap_cons, List.filterMap_append, block_cols C St y τ _ _ h1] at hi
    have hl : ((posOf u).map fun x =>
        ((St.key (num u.1.2), x, (sCol C St y τ (.tree (num u.1.2) x)).getD []) : OpenedColumn)).length =
        ((posOf u).map fun x => (u.1.1.tree - ft, x, u.1.1.W)).length := by
      rw [List.length_map, List.length_map]
    have e : ∀ (B T : List OpenedColumn) (n : ℕ) (ns : List ℕ), B.length = n →
        regroup (n :: ns) (B ++ T) = (B.map fun c => (c.2.1, c.2.2)) :: regroup ns T := by
      intro B T n ns hB
      show ((B ++ T).take n).map _ :: regroup ns ((B ++ T).drop n) = _
      rw [List.take_left' hB, List.drop_left' hB]
    rw [List.map_cons, List.map_cons, e _ _ _ _ hl] at hi
    cases i with
    | zero =>
      obtain rfl := Option.some.inj hi
      refine ⟨u, rfl, fun z hz => ?_⟩
      rw [List.map_map] at hz
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (h1 x hx)
      show sCol C St y τ (.tree (num u.1.2) x) =
        some ((sCol C St y τ (.tree (num u.1.2) x)).getD [])
      rw [hc]
      rfl
    | succ i => exact dealt_flat num ft OW h2 i grp hi

/-- **What is dealt, by the opening's number.** Rs: what the stretch drew. -/
theorem dealt_by_src (num : Fmt.TreeSource → ℕ) (ft : ℕ) (ds : List Fmt.DeclaredRound)
    (hd : ∀ d ∈ ds, d.stored = [])
    (hlen : ds.length = (drawnT C St.ds (rhoT C St.ds τ)).length)
    (hw : wantsOf St.a St.depth St.ds (drawnT C St.ds (rhoT C St.ds τ)) =
      wantsDecl num ds (drawnT C St.ds (rhoT C St.ds τ)))
    (hans : ∀ w ∈ wantsOf St.a St.depth St.ds (drawnT C St.ds (rhoT C St.ds τ)),
      (sCol C St y τ w).isSome = true)
    (i : ℕ) (grp : List (ℕ × List UInt64))
    (hi : (regroup ((groupsOf ft ds (drawnT C St.ds (rhoT C St.ds τ))).map (·.length))
      (sView C St y τ).opened)[i]? = some grp) :
    ∃ o, (ds.flatMap (·.opens))[i]? = some o ∧
      ∀ z ∈ grp, sCol C St y τ (.tree (num o.2) z.1) = some z.2 := by
  have ho : (sView C St y τ).opened =
      (wantsOf St.a St.depth St.ds (drawnT C St.ds (rhoT C St.ds τ))).filterMap
        (shown C St y τ) := rfl
  rw [hw, wantsDecl_flat num ds _ hd] at hans
  rw [ho, hw, wantsDecl_flat num ds _ hd, groupsOf_flat ft ds _ hd] at hi
  obtain ⟨u, hu, H⟩ := dealt_flat C St y τ num ft _ hans i grp hi
  refine ⟨u.1, ?_, H⟩
  rw [← H2K.First.opensWith_map ds _ hlen, List.getElem?_map, hu]
  rfl

end

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.dealt_by_src
