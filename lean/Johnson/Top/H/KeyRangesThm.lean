-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/KeyRangesThm.lean: the two lookups of the key file at full size, as written out, meet
all conditions: a theorem, by the kernel's own evaluation.

Definitions, statements and proofs. Johnson/Top/H/KeyRangesFull.lean names as a hypothesis that the
two written lookups pass the test `rangesB`, because the kernel does not reduce that test: the
sorting `List.mergeSort`, which stands in the verifier's own `Wf.coversAllRows` and in `chk2`, is
defined by well-founded recursion. This file goes round the sorting. What is asked of the two
lookups (`RangesOK`, Johnson/Top/H/KeyPortAt.lean) is shown clause by clause, each by `decide` with
the kernel, on tests without that sorting.
Main names:
  `noGap_of_cover`: the converse of `noGap_mem` (Johnson/Pack/KeyPort.lean): stretches that are
    sorted by their first numbers, begin at or below the goal and reach every number up to it pass
    the verifier's `Wf.noGap`.
  `allStretches`, `coversAllRows_of`: the verifier's test `Wf.coversAllRows` says true if `Wf.noGap`
    says true on the same stretches sorted by insertion, which the kernel reduces.
  `chk2'`, `P2_of'`: as `chk2` and `P2_of` (Johnson/Top/H/KeyPairs.lean), with the stretches in the
    order of the runs.
  `full_runs₀`, `full_runs₁`, `full_fit₀`, `full_begin₀`, `full_cover₀`, `full_chk1`, `full_chk2'`:
    the tests at the two lookups.
  `rangesOK_full`: `RangesOK lk0Full lk1Full`.


Limits: the statements are of the two values as they are written out in
Johnson/Top/H/KeyRangesFull.lean; that these are the lookups of the item "ranges" of any key file is
stated by nothing here. `HKeyRanges` itself (the value of `rangesB`) is not shown: it is not needed.
The limits of Johnson/Top/H/KeyPortAt.lean hold, but for `RangesOK`: a row number of the programs'
matrix is taken as the same row number of the library's index matrix;
nothing on multiplicities or on knowledge soundness.
-/
import Johnson.Top.H.KeyRangesFull
import Mathlib.Data.List.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.Pack
open Cm Cb
open Inst.Model.Layout (hRef)
open OnBytes.Params (WfRun WfPart WfLookup)

/-- Stretches that are sorted by their first numbers, begin at or below `goal`, and reach every
number from `upto` to `goal`, pass the verifier's test. -/
theorem noGap_of_cover (goal : ℕ) : ∀ (ss : List (ℕ × ℕ)) (upto : ℕ),
    ss.Pairwise (fun a b => a.1 ≤ b.1) → (∀ s ∈ ss, s.1 ≤ goal) →
    (∀ y, upto ≤ y → y < goal → ∃ s ∈ ss, s.1 ≤ y ∧ y < s.2) →
    OnBytes.Wf.noGap goal upto ss = true
  | [], upto, _, _, hc => by
    unfold OnBytes.Wf.noGap
    simp only [decide_eq_true_eq]
    by_contra hlt
    obtain ⟨s, hs, _⟩ := hc upto (Nat.le_refl _) (Nat.lt_of_not_le hlt)
    exact absurd hs List.not_mem_nil
  | s :: ss, upto, hp, hg, hc => by
    unfold OnBytes.Wf.noGap
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    obtain ⟨hp1, hp2⟩ := List.pairwise_cons.1 hp
    refine ⟨?_, noGap_of_cover goal ss _ hp2 (fun t ht => hg t (List.mem_cons_of_mem _ ht))
      fun y h1 h2 => ?_⟩
    · by_cases hlt : upto < goal
      · obtain ⟨t, ht, e, _⟩ := hc upto (Nat.le_refl _) hlt
        rcases List.mem_cons.1 ht with rfl | ht
        · exact e
        · exact le_trans (hp1 t ht) e
      · exact le_trans (hg s List.mem_cons_self) (Nat.le_of_not_lt hlt)
    · obtain ⟨t, ht, e1, e2⟩ := hc y (le_trans (le_max_left _ _) h1) h2
      rcases List.mem_cons.1 ht with rfl | ht
      · exact absurd e2 (Nat.not_lt.2 (le_trans (le_max_right _ _) h1))
      · exact ⟨t, ht, e1, e2⟩

/-- The stretches of rows of all runs of a lookup. -/
def allStretches (l : WfLookup) : List (ℕ × ℕ) :=
  l.parts.flatMap fun p => p.runs.map fun r => (r.firstRow, r.firstRow + r.places)

/-- The verifier's test that a lookup reaches every row, from a test of the same kind over another
sorting of the same stretches. -/
theorem coversAllRows_of (m : OnBytes.Wf.Matrix) (l : WfLookup) (hw : l.digitWeight = [1])
    (hg : ∀ s ∈ allStretches l, s.1 ≤ m.rows)
    (h : OnBytes.Wf.noGap m.rows 0
      ((allStretches l).insertionSort fun a b => a.1 ≤ b.1) = true) :
    OnBytes.Wf.coversAllRows m l = true := by
  unfold OnBytes.Wf.coversAllRows
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨hw, noGap_of_cover _ _ _ ?_ (fun s hs => hg s (List.mem_mergeSort.1 hs))
    fun y h1 h2 => ?_⟩
  · have := List.pairwise_mergeSort (le := fun a b : ℕ × ℕ => decide (a.1 ≤ b.1))
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (allStretches l)
    exact this.imp fun h => by simpa using h
  · obtain ⟨s, hs, e⟩ := noGap_mem _ _ _ h y h1 h2
    exact ⟨s, List.mem_mergeSort.2 ((List.perm_insertionSort _ _).mem_iff.1 hs), e⟩

/-- As `chk2` (Johnson/Top/H/KeyPairs.lean), with the stretches in the order of the runs. -/
def chk2' (T : List (ℕ × ℕ)) (l : WfLookup) : Bool :=
  T.all fun t => OnBytes.Wf.noGap (t.1 + t.2) t.1 (stretchesOf l t)

theorem P2_of' (l : WfLookup) (hw : l.digitWeight.length = 2) (h : chk2' unitsT l = true) :
    ∀ v < 1527800, ∃ p ∈ l.parts, ∃ ρ ∈ p.runs, ∃ u, hasPl ρ u ∧
      ∀ q < l.digitWeight.length, pairY v q = rowOf ρ u q := by
  intro v hv
  obtain ⟨t, ht, r, hr, g0, g1⟩ := pair_of v hv
  have h1 := List.all_eq_true.1 h t ht
  obtain ⟨x, hx, e1, e2⟩ := noGap_mem _ _ _ h1 (t.1 + r) (Nat.le_add_right _ _) (by omega)
  obtain ⟨p, hp, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.1 hx
  obtain ⟨hρ1, hρ2⟩ := List.mem_filter.1 hρ
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hρ2
  have hs : ρ.stride = t.2 := hρ2.1.1
  have e1' : ρ.firstRow ≤ t.1 + r := e1
  have e2' : t.1 + r < ρ.firstRow + ρ.places := e2
  refine ⟨p, hp, ρ, hρ1, ρ.firstPlace + (t.1 + r - ρ.firstRow), ⟨Nat.le_add_right _ _, by omega⟩,
    fun q hq => ?_⟩
  rw [hw] at hq
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (Nat.le_of_lt_succ hq) with rfl | rfl
  · rw [g0]
    unfold rowOf
    omega
  · rw [g1]
    unfold rowOf
    rw [hs]
    omega

/-! ### At the two lookups at full size: by the kernel's own evaluation -/

theorem full_runs₀ :
    (lk0Full.parts.all fun p => OnBytes.Wf.runsOk p.logPlaces 0 p.runs) = true := by
  decide +kernel
theorem full_runs₁ :
    (lk1Full.parts.all fun p => OnBytes.Wf.runsOk p.logPlaces 0 p.runs) = true := by
  decide +kernel
theorem full_fit₀ :
    (lk0Full.parts.all fun p => p.runs.all fun r => decide (r.firstRow + r.places ≤ hRef)) =
      true := by decide +kernel
theorem full_begin₀ : ((allStretches lk0Full).all fun s => decide (s.1 ≤ hRef)) = true := by
  decide +kernel
theorem full_cover₀ : OnBytes.Wf.noGap hRef 0
    ((allStretches lk0Full).insertionSort fun a b => a.1 ≤ b.1) = true := by decide +kernel
theorem full_chk1 : chk1 unitsT lk1Full = true := by decide +kernel
theorem full_chk2' : chk2' unitsT lk1Full = true := by decide +kernel

/-- The two lookups at full size meet all that Johnson/Top/H/KeyPortAt.lean asks. -/
theorem rangesOK_full : RangesOK lk0Full lk1Full where
  n₀ := by decide +kernel
  n₁ := by decide +kernel
  lp₀ := by decide +kernel
  lp₁ := by decide +kernel
  off₀ := by decide +kernel
  off₁ := by decide +kernel
  w₁ := rfl
  pad₀ := by decide +kernel
  pad₁ := by decide +kernel
  runs₀ := List.all_eq_true.1 full_runs₀
  runs₁ := List.all_eq_true.1 full_runs₁
  fit₀ := fun p hp r hr =>
    of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 full_fit₀ p hp) r hr)
  cov₀ := coversAllRows_of ⟨18, hRef⟩ lk0Full rfl
    (fun s hs => of_decide_eq_true (List.all_eq_true.1 full_begin₀ s hs)) full_cover₀
  P1 := P1_of lk1Full rfl full_chk1
  P2 := P2_of' lk1Full rfl full_chk2'

end Johnson.Pack

#print axioms Johnson.Pack.rangesOK_full
#print axioms Johnson.Pack.noGap_of_cover
#print axioms Johnson.Pack.coversAllRows_of
