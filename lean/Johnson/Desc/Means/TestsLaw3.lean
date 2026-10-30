-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/TestsLaw3.lean: each test of Johnson/Desc/Means/TestsB3.lean gives the invariant
that it stands for.

Main theorems: sampledMembers_of, linked_of, markedEmpty_of_test, claims_end_tested.

What is not claimed. The converses. Nothing on where a run calls the tests.

-/
import Johnson.Desc.Means.TestsB3
import Johnson.Desc.Means.TestsLaw2
import Johnson.Desc.Means.Entry
import Johnson.Desc.Means.End

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

variable {S : Statement}

theorem sampledMembers_of (h : sampledMembersB S = true) : SampledMembers S := by
  unfold sampledMembersB at h
  simp only [List.all_eq_true] at h
  intro g G hG o ho
  have c := h G (mem_of_get hG) o ho
  cases hx : S.oracles[o]? with
  | none =>
    rw [hx] at c
    cases c
  | some x =>
    rw [hx] at c
    exact ⟨x, rfl, c⟩

theorem linked_of (h : linkedB S = true) :
    ∀ (o : Nat) (x : Oracle) (g : Nat), S.oracles[o]? = some x → g ∈ x.groups →
      ∃ G, S.groups[g]? = some G ∧ o ∈ G.members := by
  unfold linkedB at h
  simp only [List.all_eq_true, List.mem_range] at h
  intro o x g hx hg
  have ho : o < S.oracles.size := by
    by_contra c
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt c)] at hx
    cases hx
  have c := h o ho
  rw [hx] at c
  have c' := List.all_eq_true.1 c g hg
  cases hG : S.groups[g]? with
  | none =>
    rw [hG] at c'
    cases c'
  | some G =>
    rw [hG] at c'
    exact ⟨G, rfl, by simpa using c'⟩

theorem markedEmpty_of_test (h : markedEmptyB S = true) :
    ∀ (i : Nat) (G : Group), S.groups[i]? = some G → G.inRun = true → G.rows = #[] := by
  unfold markedEmptyB at h
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', Array.isEmpty_iff] at h
  intro i G hG hr
  rcases h G (mem_of_get hG) with c | c
  · rw [hr] at c
    cases c
  · exact c

/-- A statement at which the four tests say yes claims nothing any more. -/
theorem claims_end_tested {K : Type} [CommRing K] (ρ : Reading K) (h1 : allTestedB S = true)
    (h2 : linkedB S = true) (h3 : markedEmptyB S = true) (h4 : noneYetB S = true) (m : Words K) :
    Claims ρ S m :=
  claims_end_of ρ h1 (linked_of h2) (markedEmpty_of_test h3) (noneYet_of h4) m

end OnBytes.Means
