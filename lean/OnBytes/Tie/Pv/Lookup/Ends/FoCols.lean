-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoCols.lean.
The columns of a call of the head's lookup: the marks that the byte-level verifier leaves on them,
against the list that says which entry of which segment stands in a column.

Head.keyForm weighs a call's columns in two ways. Each segment's form carries the weights of the
columns that the segment lists; the padding key carries the weights of the columns that stay
unmarked when every segment has marked its own (Head.markColumns, which refuses a column that is
listed twice). The call's key vector reads, column by column, the first segment that lists the
column (OnBytes.Ends.H.colH). This file shows that the two ways of summing over the columns agree.

States:
  sum_mark, marks_fold: what marking a list of columns does to a sum over the unmarked columns.
  markColumns_eq: Head.markColumns is such a marking.
  colL_hit, colL_miss: what the list of columns says at a column that a segment lists, or does not.
  cols_sum: the sum over the unmarked columns of weight times the column's term is the sum over the
    segments' entries, plus the padding's term times the weight of the columns that stay unmarked.
Premises of cols_sum: each segment lists as many columns as it has entries; Head.markColumns, run
over the segments in their order, refuses none.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoKeyFormRun
import OnBytes.Tie.Pv.Lookup.Ends.H
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Fo
open Finset OnBytes OnBytes.Model OnBytes.Ends.H

/-- A column's mark; 0 beyond the array. -/
def mk0 (w : Array ℕ) (j : ℕ) : ℕ := w.getD j 0

theorem mk0_set (w : Array ℕ) (p m j : ℕ) (hp : p < w.size) :
    mk0 (w.set! p m) j = if j = p then m else mk0 w j := by
  unfold mk0
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds]
  by_cases h : p = j
  · rw [if_pos h, if_pos hp, if_pos h.symm]
    rfl
  · rw [if_neg h, if_neg fun e => h e.symm]

/-- Marks one column, if it lies in the array and is unmarked. -/
def markStep (pos mkv : ℕ → ℕ) (w : Array ℕ) (x : ℕ) : Option (Array ℕ) :=
  if pos x < w.size && w.getD (pos x) 1 == 0 then some (w.set! (pos x) (mkv x)) else none

section
variable {K : Type} [CommRing K]

theorem sum_mark (J : ℕ) (a b : ℕ → ℕ) (f : ℕ → K) (p : ℕ) (hp : p < J) (ha : a p = 0)
    (hb : b p ≠ 0) (hab : ∀ j, j ≠ p → b j = a j) :
    ∑ j ∈ range J, (if a j = 0 then f j else 0) =
      f p + ∑ j ∈ range J, (if b j = 0 then f j else 0) := by
  have e : ∀ j ∈ range J, (if a j = 0 then f j else 0) =
      (if j = p then f j else 0) + (if b j = 0 then f j else 0) := by
    intro j _
    by_cases h : j = p
    · subst h
      rw [if_pos ha, if_pos rfl, if_neg hb, add_zero]
    · rw [if_neg h, hab j h, zero_add]
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos (mem_range.mpr hp)]

theorem marks_fold (pos mkv : ℕ → ℕ) (hm : ∀ x, mkv x ≠ 0) (f : ℕ → K) :
    ∀ (l : List ℕ) (w w' : Array ℕ), l.foldlM (markStep pos mkv) w = some w' →
      w'.size = w.size ∧ (∀ j, mk0 w j ≠ 0 → mk0 w' j ≠ 0) ∧
      (∀ x ∈ l, mk0 w' (pos x) ≠ 0 ∧ mk0 w (pos x) = 0) ∧ (l.map pos).Nodup ∧
      (∀ j, (∀ x ∈ l, pos x ≠ j) → mk0 w' j = mk0 w j) ∧
      ∑ j ∈ range w.size, (if mk0 w j = 0 then f j else 0) =
        (l.map fun x => f (pos x)).sum + ∑ j ∈ range w.size, (if mk0 w' j = 0 then f j else 0)
  | [], w, w', h => by
    have e : w = w' := Option.some.inj h
    subst e
    exact ⟨rfl, fun _ h => h, fun _ hx => absurd hx (by simp), by simp, fun _ _ => rfl, by simp⟩
  | x :: l, w, w', h => by
    rw [List.foldlM_cons] at h
    unfold markStep at h
    by_cases hc : (decide (pos x < w.size) && w.getD (pos x) 1 == 0) = true
    · rw [if_pos hc] at h
      have h' : l.foldlM (markStep pos mkv) (w.set! (pos x) (mkv x)) = some w' := h
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      obtain ⟨hp, h0⟩ := hc
      have h00 : mk0 w (pos x) = 0 := by
        unfold mk0
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hp] at h0 ⊢
        exact h0
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := marks_fold pos mkv hm f l _ w' h'
      have hs : (w.set! (pos x) (mkv x)).size = w.size := by
        rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
      have hx1 : mk0 (w.set! (pos x) (mkv x)) (pos x) ≠ 0 := by
        rw [mk0_set w _ _ _ hp, if_pos rfl]
        exact hm x
      have hne : ∀ y ∈ l, pos y ≠ pos x := fun y hy e => hx1 (e ▸ (a3 y hy).2)
      refine ⟨a1.trans hs, fun j hj => a2 j ?_, ?_, ?_, fun j hj => ?_, ?_⟩
      · rw [mk0_set w _ _ _ hp]
        split
        · exact hm x
        · exact hj
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨a2 _ hx1, h00⟩
        · refine ⟨(a3 y hy).1, ?_⟩
          have := (a3 y hy).2
          rwa [mk0_set w _ _ _ hp, if_neg (hne y hy)] at this
      · rw [List.map_cons, List.nodup_cons]
        refine ⟨fun hmem => ?_, a4⟩
        obtain ⟨y, hy, e⟩ := List.mem_map.mp hmem
        exact hne y hy e
      · rw [a5 j fun y hy => hj y (List.mem_cons_of_mem _ hy), mk0_set w _ _ _ hp,
          if_neg fun e => hj x List.mem_cons_self e.symm]
      · rw [sum_mark w.size (mk0 w) (mk0 (w.set! (pos x) (mkv x))) f (pos x) hp h00 hx1
          fun j hj => by rw [mk0_set w _ _ _ hp, if_neg hj]]
        rw [hs] at a6
        rw [a6, List.map_cons, List.sum_cons, add_assoc]
    · rw [if_neg hc] at h
      exact absurd h (by simp)

end

/-- The mark that Head.markColumns sets at entry x of a segment. -/
def markOf (R : Head.Run) (g : Seg) (x : ℕ) : ℕ :=
  if Head.perEntry g.name && Head.firstEntry R.L g.name + x ≥ R.h.V then 2 else 1

theorem markOf_ne (R : Head.Run) (g : Seg) (x : ℕ) : markOf R g x ≠ 0 := by
  unfold markOf
  split <;> decide

theorem markColumns_eq (R : Head.Run) (w : Array ℕ) (g : Seg) :
    Head.markColumns R w g =
      (List.range g.n).foldlM (markStep (fun x => g.pos.getD x 0) (markOf R g)) w := rfl

/-- Which entry of which segment of a list stands in column j. -/
def colL (l : List Seg) (j : ℕ) : Option (String × ℕ) :=
  l.findSome? fun g => (g.pos.findIdx? (· == j)).map fun x => (g.name, x)

theorem colH_eq (L : Head.HL) (q j : ℕ) : colH L q j = colL (L.calls.getD q default).segs j := rfl

theorem colL_hit (g : Seg) (l : List Seg) (x : ℕ) (hs : g.pos.size = g.n) (hx : x < g.n)
    (hn : ((List.range g.n).map fun y => g.pos.getD y 0).Nodup) :
    colL (g :: l) (g.pos.getD x 0) = some (g.name, x) := by
  have hx' : x < g.pos.size := hs ▸ hx
  have e : g.pos.findIdx? (· == g.pos.getD x 0) = some x := by
    rw [Array.findIdx?_eq_some_iff_getElem]
    refine ⟨hx', ?_, fun y hy hp => ?_⟩
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hx']
      simp
    · have hy' : y < g.pos.size := Nat.lt_trans hy hx'
      have e1 : g.pos.getD y 0 = g.pos.getD x 0 := by
        rw [Array.getD_eq_getD_getElem? (i := y), Array.getElem?_eq_getElem hy']
        simpa using hp
      have := List.nodup_iff_injective_getElem.mp hn
      have hly : y < ((List.range g.n).map fun y => g.pos.getD y 0).length := by
        simp; omega
      have hlx : x < ((List.range g.n).map fun y => g.pos.getD y 0).length := by
        simp; omega
      have h3 := @this ⟨y, hly⟩ ⟨x, hlx⟩ (by simpa using e1)
      have : y = x := congrArg Fin.val h3
      omega
  unfold colL
  rw [List.findSome?_cons_of_isSome (by rw [e]; rfl), e]
  rfl

theorem colL_miss (g : Seg) (l : List Seg) (j : ℕ) (hs : g.pos.size = g.n)
    (hj : ∀ x < g.n, g.pos.getD x 0 ≠ j) : colL (g :: l) j = colL l j := by
  have e : g.pos.findIdx? (· == j) = none := by
    rw [Array.findIdx?_eq_none_iff]
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hv
    have := hj i (hs ▸ hi)
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi] at this
    simpa using this
  unfold colL
  rw [List.findSome?_cons_of_isNone (by rw [e]; rfl)]

section
variable {K : Type} [CommRing K]

/-- The term of a column. -/
def colTerm (Φ : String → ℕ → K) (pad : K) : Option (String × ℕ) → K
  | some sx => Φ sx.1 sx.2
  | none => pad

/-- **The two ways of summing over a call's columns agree.** -/
theorem cols_sum (R : Head.Run) (E : ℕ → K) (Φ : String → ℕ → K) (pad : K) :
    ∀ (l : List Seg) (w w' : Array ℕ), (∀ g ∈ l, g.pos.size = g.n) →
      l.foldlM (Head.markColumns R) w = some w' →
      ∑ j ∈ range w.size, (if mk0 w j = 0 then E j * colTerm Φ pad (colL l j) else 0) =
        (l.map fun g => ((List.range g.n).map fun x =>
          E (g.pos.getD x 0) * Φ g.name x).sum).sum +
          pad * ∑ j ∈ range w.size, (if mk0 w' j = 0 then E j else 0)
  | [], w, w', _, h => by
    have e : w = w' := Option.some.inj h
    subst e
    rw [List.map_nil, List.sum_nil, zero_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split
    · show E j * pad = pad * E j
      ring
    · ring
  | g :: l, w, w', hs, h => by
    rw [List.foldlM_cons] at h
    cases h1 : Head.markColumns R w g with
    | none => rw [h1] at h; exact absurd h (by simp)
    | some w1 =>
      rw [h1] at h
      have h' : l.foldlM (Head.markColumns R) w1 = some w' := h
      rw [markColumns_eq] at h1
      have hg := hs g List.mem_cons_self
      obtain ⟨a1, _, a3, a4, a5, a6⟩ := marks_fold (fun x => g.pos.getD x 0) (markOf R g)
        (markOf_ne R g) (fun j => E j * colTerm Φ pad (colL (g :: l) j)) _ w w1 h1
      have ih := cols_sum R E Φ pad l w1 w' (fun g' hg' => hs g' (List.mem_cons_of_mem _ hg')) h'
      rw [a6, List.map_cons, List.sum_cons, add_assoc]
      congr 1
      · refine congrArg List.sum (List.map_congr_left fun x hx => ?_)
        rw [colL_hit g l x hg (List.mem_range.mp hx) a4]
        rfl
      · rw [a1] at ih
        rw [← ih]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : mk0 w1 j = 0
        · rw [if_pos hj, if_pos hj, colL_miss g l j hg fun x hx e =>
            (a3 x (List.mem_range.mpr hx)).1 (e ▸ hj)]
        · rw [if_neg hj, if_neg hj]

end
end Fo
