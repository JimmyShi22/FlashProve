-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/MarksReturn.lean: CONDITIONAL: on the facts ColsOK; weighed_padding also on
routed experts and an even number of layers, at least two.

What is here. The layers' own rounds (sub-protocol K4), the lookup's join: the verifier's function
weighedOf (OnBytes/Model/LayerForms.lean) marks the columns that a call's segments list, and
refuses where two list one column. The library says what the marks are WHERE IT RETURNS
(weighedOf_spec, Johnson/Road/FormsKeysRun8.lean). Here: THAT IT RETURNS, where the segments'
columns lie in the call and are all different; and that a column is left unmarked just where the
layout's own rule (CallD.padding, OnBytes/Model/Calls.lean) calls it padding. A definition of a
hypothesis; statements and proofs.

  `marks_return`     marking a list of different, unmarked indices returns.
  `ColsOK`           a call's columns: in the call, all different; the marks `used` are made of
                     them.
  `colsOn_lt`, `colsOn_nodup`   the columns that are listed on a layer.
  `weighed_returns`  weighedOf returns.
  `one_lists`        two segments that list one column are one segment.
  **`weighed_padding`**   weighedOf returns, and its marks are the layout's rule, turned round.

Not shown here. That a call with the facts ColsOK exists: no example is shown here;
ColsOfLayout.lean shows them of a layout's calls whose line is one of the library's eight, under
its eleven switches. Public data alone.
No property is claimed.
-/
import Johnson.Road.FormsKeysRun8
import Johnson.Road.FormsKeysPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env)

/-- Marking a list of different indices, none of them marked or outside the array, returns. -/
theorem marks_return : ∀ (l : List ℕ) (w : Array Bool), l.Nodup →
    (∀ i ∈ l, w.getD i true = false) → ∃ w', l.foldlM markAt w = some w'
  | [], w, _, _ => ⟨w, rfl⟩
  | i :: l, w, hn, hu => by
    obtain ⟨hni, hn'⟩ := List.nodup_cons.mp hn
    have e : markAt w i = some (w.setIfInBounds i true) := by
      unfold markAt
      rw [hu i List.mem_cons_self]
      rfl
    obtain ⟨w', hw⟩ := marks_return l (w.setIfInBounds i true) hn' fun k hk => by
      cases hc : (w.setIfInBounds i true).getD k true with
      | false => rfl
      | true =>
        rcases (getD_marked w i k).mp hc with h1 | h1
        · rw [hu k (List.mem_cons_of_mem _ hk)] at h1
          cases h1
        · exact absurd (h1 ▸ hk) hni
    refine ⟨w', ?_⟩
    rw [List.foldlM_cons, e]
    exact hw

/-- **A call's columns**: the marks `used` are made of the segments' lists; every listed column lies
in the call; no segment lists a column twice; no two segments list one column. Public. This defines
a hypothesis; the definition claims nothing. -/
structure ColsOK (c : CallD) : Prop where
  used : c.used = c.segs.foldl markUsed (Array.replicate c.J 0)
  lt : ∀ s ∈ c.segs, ∀ j ∈ s.pos.toList, j < c.J
  each : ∀ s ∈ c.segs, s.pos.toList.Nodup
  apart : c.segs.Pairwise fun s s' => List.Disjoint s.pos.toList s'.pos.toList

variable {v : Env} {c : CallD}

/-- The columns that are listed on a layer lie in the call. -/
theorem colsOn_lt (C : ColsOK c) (lam : ℕ) : ∀ j ∈ colsOn v c lam, j < c.J := by
  intro j hj
  obtain ⟨s, hs, -, hp⟩ := mem_colsOn.mp hj
  exact C.lt s hs j hp

/-- They are all different. -/
theorem colsOn_nodup (C : ColsOK c) (lam : ℕ) : (colsOn v c lam).Nodup := by
  unfold colsOn
  rw [List.nodup_flatMap]
  refine ⟨fun s hs => ?_, C.apart.imp fun {s s'} hd => ?_⟩
  · split_ifs
    · exact List.nodup_nil
    · exact C.each s hs
  · show List.Disjoint (if (s.moe && !v.isMoe lam) = true then [] else s.pos.toList)
      (if (s'.moe && !v.isMoe lam) = true then [] else s'.pos.toList)
    intro x hx hx'
    split_ifs at hx hx' <;> first
      | exact absurd hx List.not_mem_nil
      | exact absurd hx' List.not_mem_nil
      | exact hd hx hx'

/-- **weighedOf returns.** -/
theorem weighed_returns (C : ColsOK c) : ∃ w, v.weighedOf c = some w := by
  rw [weighedOf_eq]
  refine marks_return _ _ ?_ fun i hi => ?_
  · unfold marksOn
    rw [List.nodup_flatMap]
    refine ⟨fun lam _ => (colsOn_nodup C lam).map fun a b e => Nat.add_left_cancel e, ?_⟩
    rw [List.pairwise_iff_getElem]
    intro a b ha hb hab
    rw [List.getElem_range, List.getElem_range]
    intro x hx hx'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j', hj', e⟩ := List.mem_map.mp hx'
    have h1 := (layer_column (colsOn_lt C b j' hj') (colsOn_lt C a j hj) e).1
    omega
  · obtain ⟨lam, hl, j, hj, rfl⟩ := mem_marksOn.mp hi
    have hJ := colsOn_lt C lam j hj
    have hin : lam * c.J + j < v.y.Lam * c.J := by
      have h2 := Nat.mul_le_mul_right c.J (Nat.succ_le_of_lt hl)
      rw [Nat.succ_mul] at h2
      omega
    simp [Array.getD, hin]

/-- Two segments of the call that list one column are one segment. -/
theorem one_lists (C : ColsOK c) {s s' : Seg} (hs : s ∈ c.segs) (hs' : s' ∈ c.segs) {j : ℕ}
    (hj : j ∈ s.pos.toList) (hj' : j ∈ s'.pos.toList) : s = s' := by
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hs
  obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hs'
  have P := List.pairwise_iff_getElem.mp C.apart
  rcases Nat.lt_trichotomy a b with h | h | h
  · exact ((P a b ha hb h) hj hj').elim
  · subst h
    rfl
  · exact ((P b a hb ha h) hj' hj).elim

/-- **weighedOf RETURNS, AND A COLUMN IS LEFT UNMARKED JUST WHERE THE LAYOUT's RULE CALLS IT
PADDING.** CONDITIONAL: on C, on routed experts (hp3) and on an even number of layers, at least
two (hL, h0); that the number is even is asked by the proof. -/
theorem weighed_padding (C : ColsOK c) (hp3 : v.y.h.p3 = true) (hL : v.y.Lam % 2 = 0)
    (h0 : 0 < v.y.Lam) :
    ∃ w, v.weighedOf c = some w ∧ w.size = v.y.Lam * c.J ∧
      ∀ lam, lam < v.y.Lam → ∀ j, j < c.J →
        w.getD (lam * c.J + j) true = !c.padding lam j := by
  obtain ⟨w, hw⟩ := weighed_returns (v := v) C
  have hodd : (v.y.Lam - 1) % 2 = 1 := by omega
  have hlast : ∀ s ∈ c.segs, (s.moe && !v.isMoe (v.y.Lam - 1)) = false := by
    intro s _
    unfold Env.isMoe
    rw [hp3, hodd]
    simp
  obtain ⟨hsz, hall⟩ := weighedOf_spec hw hlast
  refine ⟨w, hw, hsz, fun lam hl j hj => ?_⟩
  obtain ⟨_, _, hiff⟩ := hall lam hl
  have hu : j < (Array.replicate c.J 0).size := by
    rw [Array.size_replicate]
    exact hj
  have hz : (Array.replicate c.J 0).getD j 0 = 0 := by simp [Array.getD, hj]
  by_cases hex : ∃ s ∈ c.segs, j ∈ s.pos.toList
  · obtain ⟨s, hs, hjs⟩ := hex
    have hmk : ∀ s2 ∈ c.segs, j ∈ s2.pos.toList → markOf s2 = markOf s := fun s2 h2 hj2 => by
      rw [one_lists C h2 hs hj2 hjs]
    have hus : c.used.getD j 0 = markOf s := by
      rw [C.used]
      exact (used_get (markOf s) j c.segs _ hu hmk).1 ⟨s, hs, hjs⟩
    have hin : j ∈ colsOn v c lam ↔ (s.moe && !v.isMoe lam) = false := by
      rw [mem_colsOn]
      constructor
      · rintro ⟨s2, h2, hb, hj2⟩
        rw [← one_lists C h2 hs hj2 hjs]
        exact hb
      · exact fun hb => ⟨s, hs, hb, hjs⟩
    have hpad : c.padding lam j = (s.moe && !v.isMoe lam) := by
      show (c.used.getD j 0 == 0 || (c.used.getD j 0 == 2 && lam % 2 == 0)) = _
      rw [hus]
      unfold markOf Env.isMoe
      rw [hp3]
      cases s.moe <;> rcases Nat.mod_two_eq_zero_or_one lam with e | e <;> simp [e]
    rw [hpad]
    cases hb : (s.moe && !v.isMoe lam) with
    | false => exact (hiff j hj).mpr (hin.mpr hb)
    | true =>
      cases hg : w.getD (lam * c.J + j) true with
      | false => rfl
      | true =>
        have := hin.mp ((hiff j hj).mp hg)
        rw [hb] at this
        cases this
  · have hno : ∀ s ∈ c.segs, j ∉ s.pos.toList := fun s hs hjs => hex ⟨s, hs, hjs⟩
    have hus : c.used.getD j 0 = 0 := by
      rw [C.used, (used_get 0 j c.segs _ hu fun s hs hm => absurd hm (hno s hs)).2 hno, hz]
    have hpad : c.padding lam j = true := by
      show (c.used.getD j 0 == 0 || (c.used.getD j 0 == 2 && lam % 2 == 0)) = true
      rw [hus]
      rfl
    rw [hpad]
    cases hg : w.getD (lam * c.J + j) true with
    | false => rfl
    | true =>
      obtain ⟨s, hs, -, hjs⟩ := mem_colsOn.mp ((hiff j hj).mp hg)
      exact absurd hjs (hno s hs)

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.marks_return
#print axioms OnBytes.Road.K4.C.colsOn_lt
#print axioms OnBytes.Road.K4.C.colsOn_nodup
#print axioms OnBytes.Road.K4.C.weighed_returns
#print axioms OnBytes.Road.K4.C.one_lists
#print axioms OnBytes.Road.K4.C.weighed_padding
