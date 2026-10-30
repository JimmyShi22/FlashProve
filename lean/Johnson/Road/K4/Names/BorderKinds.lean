-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Names/BorderKinds.lean: OF WHICH SORT EACH MATRIX OF A LAYERS' SUB-PROOF IS, BY THE
MAKERS' OWN TEXTS: what bordersOf (OnBytes/Model/LayerPlan.lean) keeps and lays, matrix by matrix,
and the field kind in the lists of tailsOf. No scope is asked.

  `bord y x`: bordersOf's own first test on a matrix with its number.
  `bstep y`: bordersOf's step, by projections. `fold_log`: a fold that writes one entry a step.
  `at_of_map`, `getD_map_range`: an entry of a mapped list; an entry of a mapped range.
  **`bordersOf_kinds`**: the two lists are as long as the list that went in; at each μ: the field
    kind is kept; txOf has a number just where bord accepts; a matrix of kind 1 has its field
    foreign laid. Premise: bordersOf returns.
  **`tails_kind`**: in tailsOf's list of group g the field kind is 1 at the stream that comes in
    of a later group, else 0.
The walk is that of bordersOf_labels (Johnson/Road/HeadDict.lean).
Limits. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.HeadDict
import Johnson.Road.K4.Names.ShapePx

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Names
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Lay bordersOf tailsOf matIx)
open OnBytes.Road (ok_of_refuse)

/-- bordersOf's own first test on a matrix with its number. -/
def bord (y : Lay) (x : TMat × Nat) : Bool :=
  x.1.kind == 0 && (x.2 == (matIx y).iXO || (y.h.p4 && x.2 == (matIx y).iQA))

/-- bordersOf's step, by projections. -/
def bstep (y : Lay) (s : Array TMat × Array (Option Nat) × Array T2Foreign × Nat)
    (x : TMat × Nat) : Array TMat × Array (Option Nat) × Array T2Foreign × Nat :=
  if bord y x = true then (s.1.push x.1, s.2.1.push (some s.2.2.2), s.2.2.1, s.2.2.2 + 1)
  else if (x.1.kind == 1) = true then
    (s.1.push { x.1 with foreign := some s.2.2.1.size, ttOff := 0 }, s.2.1.push none,
     s.2.2.1.push { name := "PXf" ++ toString s.2.2.1.size, K := x.1.k, a := 2, m := x.1.m,
                    wp := x.1.wp }, s.2.2.2)
  else (s.1.push x.1, s.2.1.push none, s.2.2.1, s.2.2.2)

/-- A fold that writes one entry a step. -/
theorem fold_log {σ α β : Type} (F : σ → α → σ) (obs : σ → List β) (w : α → β)
    (hstep : ∀ s x, obs (F s x) = obs s ++ [w x]) :
    ∀ (l : List α) (s : σ), obs (l.foldl F s) = obs s ++ l.map w
  | [], s => by simp
  | x :: l, s => by
    rw [List.foldl_cons, fold_log F obs w hstep l, hstep, List.map_cons, List.append_assoc]
    rfl

theorem bstep_kind (y : Lay) (s : Array TMat × Array (Option Nat) × Array T2Foreign × Nat)
    (x : TMat × Nat) :
    ((bstep y s x).1.toList.map fun M => M.kind) =
      (s.1.toList.map fun M => M.kind) ++ [x.1.kind] := by
  unfold bstep
  split_ifs <;> simp

theorem bstep_tx (y : Lay) (s : Array TMat × Array (Option Nat) × Array T2Foreign × Nat)
    (x : TMat × Nat) :
    ((bstep y s x).2.1.toList.map fun o => o.isSome) =
      (s.2.1.toList.map fun o => o.isSome) ++ [bord y x] := by
  unfold bstep
  by_cases h : bord y x = true
  · rw [if_pos h, h]
    simp
  · rw [if_neg h, Bool.eq_false_iff.2 h]
    split_ifs <;> simp

theorem bstep_for (y : Lay) (s : Array TMat × Array (Option Nat) × Array T2Foreign × Nat)
    (x : TMat × Nat) :
    ((bstep y s x).1.toList.map fun M => M.kind != 1 || M.foreign.isSome) =
      (s.1.toList.map fun M => M.kind != 1 || M.foreign.isSome) ++ [true] := by
  unfold bstep
  by_cases h : bord y x = true
  · rw [if_pos h]
    have h0 : x.1.kind = 0 := by
      unfold bord at h
      rw [Bool.and_eq_true] at h
      simpa using h.1
    simp [h0]
  · rw [if_neg h]
    by_cases h1 : (x.1.kind == 1) = true
    · rw [if_pos h1]
      simp
    · rw [if_neg h1]
      have h2 : (x.1.kind != 1) = true := by
        rw [bne, Bool.eq_false_iff.2 h1]
        rfl
      simp [h2]

/-- An entry of a mapped list, at a number below the length. -/
theorem at_of_map {α β γ : Type} {l : List α} {l' : List γ} {u : α → β} {v : γ → β}
    (e : l.map u = l'.map v) {μ : Nat} {a : α} {c : γ} (ha : l[μ]? = some a)
    (hc : l'[μ]? = some c) : u a = v c := by
  have h := congrArg (·[μ]?) e
  simp only [List.getElem?_map, ha, hc, Option.map_some] at h
  exact Option.some.inj h

variable {y : Lay} {ms mats : Array TMat} {txOf : Array (Option Nat)} {ft : Array T2Foreign}

/-- **What bordersOf keeps and lays, matrix by matrix.** -/
theorem bordersOf_kinds (h : bordersOf y ms = .ok (mats, txOf, ft)) :
    mats.size = ms.size ∧ txOf.size = ms.size ∧
      ∀ μ, μ < ms.size → (mats.getD μ {}).kind = (ms.getD μ {}).kind ∧
        (txOf.getD μ none).isSome = bord y (ms.getD μ {}, μ) ∧
        ((mats.getD μ {}).kind = 1 → ∃ j, (mats.getD μ {}).foreign = some j) := by
  unfold bordersOf at h
  obtain ⟨-, h⟩ := ok_of_refuse h
  have e := Except.ok.inj h
  have e1 : (ms.toList.zipIdx.foldl (bstep y) (#[], #[], #[], 0)).1 = mats :=
    congrArg Prod.fst e
  have e2 : (ms.toList.zipIdx.foldl (bstep y) (#[], #[], #[], 0)).2.1 = txOf :=
    congrArg (fun r => r.2.1) e
  have k1 := fold_log (bstep y) (fun s => s.1.toList.map fun M => M.kind) (fun x => x.1.kind)
    (bstep_kind y) ms.toList.zipIdx (#[], #[], #[], 0)
  have k2 := fold_log (bstep y) (fun s => s.2.1.toList.map fun o => o.isSome) (bord y)
    (bstep_tx y) ms.toList.zipIdx (#[], #[], #[], 0)
  have k3 := fold_log (bstep y)
    (fun s => s.1.toList.map fun M => M.kind != 1 || M.foreign.isSome) (fun _ => true)
    (bstep_for y) ms.toList.zipIdx (#[], #[], #[], 0)
  dsimp only at k1 k2 k3
  rw [e1] at k1 k3
  rw [e2] at k2
  simp only [Array.toList_empty, List.map_nil, List.nil_append] at k1 k2 k3
  have s1 : mats.size = ms.size := by
    have := congrArg List.length k1
    simpa using this
  have s2 : txOf.size = ms.size := by
    have := congrArg List.length k2
    simpa using this
  refine ⟨s1, s2, fun μ hμ => ?_⟩
  have hz : ms.toList.zipIdx[μ]? = some (ms.getD μ {}, μ) := by
    rw [List.getElem?_zipIdx, Array.getElem?_toList, Array.getElem?_eq_getElem hμ,
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hμ]
    simp
  have hm : mats.toList[μ]? = some (mats.getD μ {}) := by
    rw [Array.getElem?_toList, Array.getElem?_eq_getElem (by omega),
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
    rfl
  have ht : txOf.toList[μ]? = some (txOf.getD μ none) := by
    rw [Array.getElem?_toList, Array.getElem?_eq_getElem (by omega),
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
    rfl
  refine ⟨at_of_map k1 hm hz, at_of_map k2 ht hz, fun hk => ?_⟩
  have h3 : ((mats.getD μ {}).kind != 1 || (mats.getD μ {}).foreign.isSome) = true :=
    at_of_map k3 hm hz
  rw [hk] at h3
  exact Option.isSome_iff_exists.1 (by simpa using h3)

/-- An entry of a mapped range. -/
theorem getD_map_range {α : Type} (f : Nat → α) {n g : Nat} (hg : g < n) (d : α) :
    ((Array.range n).map f).getD g d = f g := by
  have hs : g < ((Array.range n).map f).size := by
    rw [Array.size_map, Array.size_range]
    exact hg
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs, Array.getElem_map,
    Array.getElem_range]
  rfl

/-- **The field kind in tailsOf's lists.** -/
theorem tails_kind {g μ : Nat} (hg : g < y.NGr) (hμ : μ < ((tailsOf y).getD g {}).mats.size) :
    (((tailsOf y).getD g {}).mats.getD μ {}).kind =
      if (μ == (matIx y).iXI && g != 0) = true then 1 else 0 := by
  unfold tailsOf at hμ ⊢
  dsimp only at hμ ⊢
  rw [getD_map_range _ hg] at hμ ⊢
  dsimp only at hμ ⊢
  rw [List.size_toArray, List.length_map] at hμ
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map,
    List.getElem?_eq_getElem hμ]
  simp only [Option.map_some, Option.getD_some, List.getElem_zipIdx, Nat.zero_add]
  split_ifs <;> rfl

end OnBytes.Road.K4.Names

#print axioms OnBytes.Road.K4.Names.bordersOf_kinds
#print axioms OnBytes.Road.K4.Names.tails_kind
