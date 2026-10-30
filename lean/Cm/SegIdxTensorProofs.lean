-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegIdxTensorProofs.lean: the proofs of the statements of Cm/SegIdxTensor.lean (the index atom of
a weight tensor). `t_ok` and `t_vtx` come from those on units (Cm/SegIdxUnitProofs.lean): under
`WidthsOK` the runs that `cutBits` makes fit (`fitsAll_cut`) and together are the bits given
(`all_cut`), so they name the same variables, each as often; the row part of an index is in range
exactly if the index is, or the coordinate lies wholly in the column bits (`live_iff`).
-/
import Cm.SegIdxTensor
import Cm.SegIdxUnitProofs
import Inst.Model.LayoutSplit

set_option autoImplicit false

namespace Cm
open Cb Blocks Finset Inst.Model Inst.Model.Layout

theorem of_ok (c : Coord) (left : ℕ) (σ : List Src) (h : WidthOK c σ) :
    (CSrc.of c (tOf c left) σ).Fits c (tOf c left) ∧ (CSrc.of c (tOf c left) σ).all = σ := by
  obtain ⟨hR, hle, hw⟩ := h
  have hs : sOf c.R ≤ σ.length := Tensor.sOf_le_of_le hR hle
  refine of_fits c _ σ (fun hk => ?_) (fun hk => ?_) (fun hk ht => ?_)
  · have : tOf c left = min (sOf c.R) left := by unfold tOf; rw [hk]
    rw [this]
    exact le_trans (Nat.min_le_left _ _) hs
  · have : tOf c left = min (sOf c.R) left := by unfold tOf; rw [hk]
    rw [this]
    exact ⟨Nat.min_le_left _ _, hs⟩
  · have e : tOf c left =
      if Nat.clog 2 c.R ≤ left then Nat.clog 2 c.R else 0 := by unfold tOf; rw [hk]
    rw [e] at ht ⊢
    split_ifs at ht ⊢ with h1
    · exact hw hk
    · exact absurd ht (Nat.lt_irrefl 0)

theorem fitsAll_cut :
    ∀ (cs : List Coord) (left : ℕ) (σs : List (List Src)),
      WidthsOK cs σs → FitsAll cs left (cutBits cs left σs)
  | [], _, [], _ => trivial
  | c :: cs, left, σ :: σs, h => ⟨(of_ok c left σ h.1).1, fitsAll_cut cs _ σs h.2⟩
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim

theorem all_cut :
    ∀ (cs : List Coord) (left : ℕ) (σs : List (List Src)),
      WidthsOK cs σs → (cutBits cs left σs).map CSrc.all = σs
  | [], _, [], _ => rfl
  | c :: cs, left, σ :: σs, h => by
      show (CSrc.of c (tOf c left) σ).all :: (cutBits cs (left - tOf c left) σs).map CSrc.all =
        σ :: σs
      rw [(of_ok c left σ h.1).2, all_cut cs _ σs h.2]
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim

theorem idxAt_eq (xs : List CSrc) (v b : ℕ) : idxAt xs v b = numsAt (xs.map CSrc.all) v b := by
  unfold idxAt numsAt
  rw [List.map_map]
  rfl

/-- the sources of a unit name the variables of all bits of its indices, each as often -/
theorem count_allSrc (a : ℕ) :
    ∀ xs : List CSrc, (Src.vars (allSrc xs)).count a = (Src.vars (xs.map CSrc.all).flatten).count a
  | [] => rfl
  | x :: xs => by
      have ih := count_allSrc a xs
      unfold allSrc at ih ⊢
      show (Src.vars ((colSrc xs ++ x.B) ++ (rowSrc xs ++ (x.A ++ x.C)))).count a =
        (Src.vars ((x.A ++ x.B ++ x.C) ++ (xs.map CSrc.all).flatten)).count a
      simp only [vars_append, List.count_append] at ih ⊢
      omega

theorem ok_allSrc {xs : List CSrc} {v : ℕ} (h : Src.OK (xs.map CSrc.all).flatten v) :
    Src.OK (allSrc xs) v := by
  have hp : (Src.vars (allSrc xs)).Perm (Src.vars (xs.map CSrc.all).flatten) :=
    List.perm_iff_count.2 fun a => count_allSrc a xs
  exact ⟨hp.nodup_iff.2 h.1, fun u hu => h.2 u (hp.mem_iff.1 hu)⟩

theorem live_iff : Spec.live_iff := by
  intro c left i
  constructor
  · intro h
    by_contra hn
    rw [not_or, not_lt] at hn
    obtain ⟨hw, hi⟩ := hn
    refine absurd h (not_lt.2 ?_)
    obtain ⟨R, kind⟩ := c
    cases kind with
    | low => exact Nat.div_le_div_right hi
    | high =>
      have ht : tOf ⟨R, .high⟩ left ≤ sOf R := Nat.min_le_left _ _
      generalize tOf ⟨R, .high⟩ left = t at ht
      show R / 2 ^ t ≤ (i / 2 ^ sOf R) * 2 ^ (sOf R - t) + i % 2 ^ (sOf R - t)
      obtain ⟨q, hq⟩ := Tensor.two_pow_sOf_dvd R
      have hp : (2 : ℕ) ^ sOf R = 2 ^ (sOf R - t) * 2 ^ t := by
        rw [← pow_add, Nat.sub_add_cancel ht]
      have e1 : R / 2 ^ t = q * 2 ^ (sOf R - t) := by
        conv_lhs => rw [hq, hp]
        rw [show 2 ^ (sOf R - t) * 2 ^ t * q = (q * 2 ^ (sOf R - t)) * 2 ^ t by ring]
        exact Nat.mul_div_cancel _ (Nat.two_pow_pos t)
      have e2 : q ≤ i / 2 ^ sOf R := by
        rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), Nat.mul_comm, ← hq]
        exact hi
      rw [e1]
      exact le_trans (Nat.mul_le_mul_right _ e2) (Nat.le_add_right _ _)
    | whole =>
      have ht : ¬ 0 < tOf ⟨R, .whole⟩ left := fun h0 => hw ⟨rfl, h0⟩
      show (if 0 < tOf ⟨R, .whole⟩ left then 1 else R) ≤
        (if 0 < tOf ⟨R, .whole⟩ left then (i, 0) else (0, i)).2
      rw [if_neg ht, if_neg ht]
      exact hi
  · rintro (⟨hk, ht⟩ | hi)
    · obtain ⟨R, kind⟩ := c
      have hk : kind = .whole := hk
      subst hk
      show (if 0 < tOf ⟨R, .whole⟩ left then (i, 0) else (0, i)).2 <
        (if 0 < tOf ⟨R, .whole⟩ left then 1 else R)
      rw [if_pos ht, if_pos ht]
      exact Nat.one_pos
    · exact ((Bridge.good_split c left).lt i hi).2

theorem liveAt_iff :
    ∀ (cs : List Coord) (left : ℕ) (is : List ℕ), LiveAt cs left is ↔ InRows cs left is
  | [], _, _ => Iff.rfl
  | _ :: _, _, [] => Iff.rfl
  | c :: cs, left, i :: is => and_congr (live_iff c left i) (liveAt_iff cs _ is)

theorem t_ok : Spec.t_ok := by
  intro F _ E _ _ Φ v P n U σs hw hOK
  refine unit_ok F E Φ v P n U _ (fitsAll_cut _ _ _ hw) (ok_allSrc ?_)
  rw [all_cut _ _ _ hw]
  exact hOK

theorem t_vtx : Spec.t_vtx := by
  classical
  intro F _ E _ _ Φ v P n U σs hw hfit W b
  rw [tAtom, unit_vtx F E Φ v P n U _ (fitsAll_cut _ _ _ hw) hfit W b, idxAt_eq, all_cut _ _ _ hw]
  exact if_congr (liveAt_iff _ _ _) rfl rfl

theorem entry_cast : Spec.entry_cast := by
  intro R _ P k M n U i
  unfold entryW entry
  push_cast
  rfl

end Cm
