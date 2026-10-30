-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PlaceOff.lean: at which place the verifier's placing puts each panel of the batched
sumcheck of a layers' sub-proof, and that this is the library's place.

placePanels (OnBytes/Model/LayerPanels.lean) sorts the panels' numbers by the panels' bits, the
largest first, with a merge sort, and lays the panels end to end from 0. The library's offP
(Inst/Model/FF/Objects.lean) is a sum: the sizes of all panels that have more bits, or as many and
stand earlier in the list. Johnson/Road/FormsKeysPans.lean (placed_are_pans) says that the two lists
go member by member and in order, and leaves open which place a panel gets.

Main names:
  `placedBefore`: panel j has more bits than panel i, or as many and a smaller number.
  `placeOrder_before`: in the order of the placing, an earlier number is placedBefore a later one
    (the merge sort keeps the list's order among panels of one size).
  `place_off_split`: a panel's first place is the first free place at the start plus the sizes of
    the panels that are placed before it.
  `placePanels_off`: so the first place of panel i is the sum of the sizes of the panels j that are
    placedBefore i.
  `placed_offP`: if the list has as many panels as the library's list pans D, and panel j has the
    bits of the library's panel number j, the first place of panel i is offP D of the library's
    panel number i.
Limits. Arithmetic on placePanels alone. That the verifier's panels have the library's numbers of
bits is a premise of placed_offP (hw); nothing here shows it. Nothing on the panels' sides, on a
run, on soundness or on hiding.


-/
import Johnson.Road.FormsKeysPan
import Cb.Pv.Lay.End.SigC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4

open OnBytes.Model.Layer (SBlk placePanels)
open Inst.Model.FFSeg (Dim Pan pans offP)

/-- Panel j has more bits than panel i, or as many and a smaller number. -/
def placedBefore (bl : Array SBlk) (j i : ℕ) : Prop :=
  wOf bl i < wOf bl j ∨ (wOf bl j = wOf bl i ∧ j < i)

instance (bl : Array SBlk) (j i : ℕ) : Decidable (placedBefore bl j i) := by
  unfold placedBefore
  infer_instance

/-- Two numbers in rising order are a sublist of the list of the numbers below n. -/
theorem pair_sub_range : ∀ (n : ℕ) {a b : ℕ}, b < a → a < n → [b, a].Sublist (List.range n)
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, a, b, hba, han => by
    rw [List.range_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp han with h | h
    · exact List.sublist_append_of_sublist_left (pair_sub_range n hba h)
    · subst h
      exact (List.singleton_sublist.mpr (List.mem_range.mpr hba)).append (List.Sublist.refl [a])

/-- In a list without repeats two members do not stand in both orders. -/
theorem no_both : ∀ {l : List ℕ}, l.Nodup → ∀ {a b : ℕ}, [a, b].Sublist l → [b, a].Sublist l → False
  | [], _, _, _, h1, _ => by cases h1
  | x :: l, hn, a, b, h1, h2 => by
    have hn' := List.nodup_cons.mp hn
    cases h1 with
    | cons _ h1 =>
      cases h2 with
      | cons _ h2 => exact no_both hn'.2 h1 h2
      | cons₂ _ _ => exact hn'.1 (h1.subset (by simp))
    | cons₂ _ h1 =>
      cases h2 with
      | cons _ h2 => exact hn'.1 (h2.subset (by simp))
      | cons₂ _ h2 => exact hn'.1 (h2.subset (by simp))

/-- In the order of the placing an earlier number is placedBefore a later one. -/
theorem placeOrder_before (bl : Array SBlk) : (placeOrder bl).Pairwise (placedBefore bl) := by
  obtain ⟨hs, hn, hm⟩ := placeOrder_spec bl
  rw [List.pairwise_iff_forall_sublist]
  intro a b hab
  have hw : wOf bl b ≤ wOf bl a := List.pairwise_iff_forall_sublist.mp hs hab
  have hne : a ≠ b := List.pairwise_iff_forall_sublist.mp hn hab
  have ha : a < bl.size := (hm a).mp (hab.subset (by simp))
  unfold placedBefore
  rcases Nat.lt_or_ge (wOf bl b) (wOf bl a) with h | h
  · exact Or.inl h
  · refine Or.inr ⟨Nat.le_antisymm h hw, ?_⟩
    rcases Nat.lt_or_ge a b with h' | h'
    · exact h'
    · exfalso
      have hba : b < a := Nat.lt_of_le_of_ne h' (Ne.symm hne)
      have st : [b, a].Sublist (placeOrder bl) := List.pair_sublist_mergeSort
        (le := fun a b => decide ((bl.getD b {}).w ≤ (bl.getD a {}).w))
        (fun a b c h1 h2 => by
          simp only [decide_eq_true_eq] at h1 h2 ⊢
          omega)
        (fun a b => by
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          omega)
        (by
          simp only [decide_eq_true_eq]
          exact h)
        (pair_sub_range bl.size hba ha)
      exact no_both hn hab st

/-- A panel's first place: the first free place at the start, plus the sizes of the panels that are
placed before it. -/
theorem place_off_split (bl : Array SBlk) : ∀ (l1 l2 : List ℕ) (i : ℕ) (s : Array SBlk × ℕ),
    (l1 ++ i :: l2).Nodup → i < s.1.size →
    (((l1 ++ i :: l2).foldl (placeStep bl) s).1.getD i {}).off =
      s.2 + (l1.map fun j => 2 ^ wOf bl j).sum
  | [], l2, i, s, hn, hi => by
    have hn' := List.nodup_cons.mp hn
    rw [List.nil_append, List.foldl_cons, place_other bl l2 _ i hn'.1, placeStep_self bl s i hi]
    simp
  | a :: l1, l2, i, s, hn, hi => by
    have hn' := List.nodup_cons.mp hn
    rw [List.cons_append, List.foldl_cons,
      place_off_split bl l1 l2 i (placeStep bl s a) hn'.2 (by simpa [placeStep] using hi),
      List.map_cons, List.sum_cons]
    show s.2 + 2 ^ wOf bl a + _ = _
    omega

/-- **The first place of panel i**: the sum of the sizes of the panels that are placedBefore i. -/
theorem placePanels_off (bl : Array SBlk) {i : ℕ} (hi : i < bl.size) :
    ((placePanels bl).1.getD i {}).off =
      ((List.range bl.size).map fun j => if placedBefore bl j i then 2 ^ wOf bl j else 0).sum := by
  obtain ⟨_, hn, hm⟩ := placeOrder_spec bl
  have hb := placeOrder_before bl
  have perm : (placeOrder bl).Perm (List.range bl.size) := List.mergeSort_perm _ _
  obtain ⟨l1, l2, e⟩ := List.append_of_mem ((hm i).mpr hi)
  rw [← (perm.map fun j => if placedBefore bl j i then 2 ^ wOf bl j else 0).sum_eq, placePanels_eq]
  rw [e] at hn hb ⊢
  rw [place_off_split bl l1 l2 i (bl, 0) hn hi, List.map_append, List.sum_append, List.map_cons,
    List.sum_cons]
  obtain ⟨_, h2, h12⟩ := List.pairwise_append.mp hb
  have h2' := List.pairwise_cons.mp h2
  have e1 : (l1.map fun j => if placedBefore bl j i then 2 ^ wOf bl j else 0) =
      l1.map fun j => 2 ^ wOf bl j :=
    List.map_congr_left fun j hj => if_pos (h12 j hj i List.mem_cons_self)
  have e2 : (l2.map fun j => if placedBefore bl j i then 2 ^ wOf bl j else 0) =
      l2.map fun _ => 0 :=
    List.map_congr_left fun j hj => if_neg fun c => by
      have c' := h2'.1 j hj
      unfold placedBefore at c c'
      omega
  have e0 : ¬ placedBefore bl i i := fun c => by
    unfold placedBefore at c
    omega
  rw [e1, e2, if_neg e0]
  simp

/-- A list's image, written over the numbers of its members. -/
theorem map_as_range {α : Type} (L : List α) (f : α → ℕ) :
    L.map f = (List.range L.length).map fun j => if h : j < L.length then f L[j] else 0 := by
  apply List.ext_getElem
  · simp
  · intro j h1 _
    have hj : j < L.length := by simpa using h1
    simp [hj]

/-- **The verifier's place is the library's**, for a list that has the library's numbers of bits,
member by member. -/
theorem placed_offP (D : Dim) (bl : Array SBlk) (hl : bl.size = (pans D).length)
    (hw : ∀ j (h : j < (pans D).length), wOf bl j = ((pans D)[j]).wid D) {i : ℕ}
    (hi : i < (pans D).length) :
    ((placePanels bl).1.getD i {}).off = offP D (pans D)[i] := by
  have hn := Cb.Pv.Lay.End.Sig.pans_nodup D
  rw [placePanels_off bl (by rw [hl]; exact hi), Cb.Pv.Lay.End.Sig.offP_eq,
    map_as_range (pans D), hl]
  refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
  have hj' : j < (pans D).length := List.mem_range.mp hj
  rw [dif_pos hj', hw j hj']
  have iff : placedBefore bl j i ↔ Cb.Pv.Lay.End.Sig.before D (pans D)[j] (pans D)[i] := by
    unfold placedBefore Cb.Pv.Lay.End.Sig.before
    rw [hw j hj', hw i hi, hn.idxOf_getElem j hj', hn.idxOf_getElem i hi]
  by_cases c : placedBefore bl j i
  · rw [if_pos c, if_pos (iff.mp c)]
  · rw [if_neg c, if_neg fun c' => c (iff.mpr c')]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.placePanels_off
#print axioms OnBytes.Road.K4.placed_offP
