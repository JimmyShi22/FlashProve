-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/TestsLaw2.lean: each test of Johnson/Desc/Means/TestsB2.lean gives the invariant
that it stands for.

Main theorems: inOrder_of, openKinds_of, noneYet_of, tidy_gives.

What is not claimed. The converses. Nothing on where a run calls the tests.

-/
import Johnson.Desc.Means.TestsB2
import Johnson.Desc.Means.TestsLaw
import Johnson.Desc.Means.Back

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

variable {S : Statement}

theorem mem_of_get {α : Type} {A : Array α} {i : Nat} {a : α} (h : A[i]? = some a) :
    a ∈ A.toList :=
  Array.mem_toList_iff.2 (Array.mem_of_getElem? h)

theorem inOrder_of (h : inOrderB S = true) : InOrder S := by
  unfold inOrderB at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun g G hG => groupOk_of (h1 G (mem_of_get hG)).1,
    fun g G hG r hr => rowIn_of ((h1 G (mem_of_get hG)).2 r hr), fun o x hx r hr => ?_⟩
  have ho : o < S.oracles.size := by
    by_contra c
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt c)] at hx
    cases hx
  have c := h2 o ho
  rw [hx] at c
  exact rowIn_of (List.all_eq_true.1 c r hr)

theorem openKinds_of (h : openKindsB S = true) : OpenKinds S := by
  unfold openKindsB at h
  simp only [List.all_eq_true, bne_iff_ne, ne_eq] at h
  exact fun g G hG r hr => h G (mem_of_get hG) r hr

theorem noneYet_of (h : noneYetB S = true) : NoneYet S := by
  unfold noneYetB at h
  simp only [List.all_eq_true, Bool.or_eq_true, Array.isEmpty_iff] at h
  intro o x hx hs
  rcases h x (mem_of_get hx) with c | c
  · rw [hs] at c
    cases c
  · exact c

/-- The test gives the three invariants. -/
theorem tidy_gives (h : tidyB S = true) : InOrder S ∧ OpenKinds S ∧ NoneYet S := by
  unfold tidyB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨inOrder_of h.1.1, openKinds_of h.1.2, noneYet_of h.2⟩

end OnBytes.Means
