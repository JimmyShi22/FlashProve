-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/TestsBack.lean: the converses of Johnson/Desc/Means/TestsLaw.lean, TestsLaw2.lean
and TestsLaw3.lean for the four invariants on a statement: where the invariant holds its test with
code says yes. So each test says yes exactly where its invariant holds, and a promise that holds the
test can be kept by a step that keeps the invariant.

Main definition: tidy4B: all four tests. Main theorems: groupOkB_iff, rowInB_iff, inOrderB_iff,
openKindsB_iff, noneYetB_iff, sampledMembersB_iff, tidyB_iff, tidy4B_iff (tidy4B S = true exactly
where Tidy S).

What is not claimed. Nothing on where a run calls the tests. Nothing on soundness.

-/
import Johnson.Desc.Means.TestsLaw3
import Johnson.Desc.Means.Walk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

variable {S : Statement}

theorem get_of_mem {α : Type} {A : Array α} {a : α} (h : a ∈ A.toList) :
    ∃ i : Nat, A[i]? = some a := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 h
  exact ⟨i, by simpa using hi⟩

theorem distinct_of_nodup : ∀ l : List Nat, l.Nodup → distinctNats l = true
  | [], _ => by unfold distinctNats; rfl
  | a :: l, h => by
    unfold distinctNats
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not]
    exact ⟨(List.nodup_cons.1 h).1, distinct_of_nodup l (List.nodup_cons.1 h).2⟩

theorem groupOkB_of {G : Group} (h : GroupOk S G) : groupOkB S G = true := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  unfold groupOkB
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine ⟨⟨⟨distinct_of_nodup _ h1, h2⟩, h3⟩, fun o ho => ?_⟩
  split
  · rename_i x hx
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
    exact ⟨h4 o ho x hx, h5 o ho x hx⟩
  · rfl

theorem groupOkB_iff {G : Group} : groupOkB S G = true ↔ GroupOk S G := ⟨groupOk_of, groupOkB_of⟩

theorem rowInB_of {G : Group} {row : Row} (h : RowIn S G row) : rowInB S G row = true := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  unfold rowInB
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨h1, h2⟩, fun w hw => ⟨⟨(h3 w hw).1, (h3 w hw).2.1⟩, (h3 w hw).2.2⟩⟩, h4⟩

theorem rowInB_iff {G : Group} {row : Row} : rowInB S G row = true ↔ RowIn S G row :=
  ⟨rowIn_of, rowInB_of⟩

theorem inOrderB_of (h : InOrder S) : inOrderB S = true := by
  unfold inOrderB
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range]
  refine ⟨fun G hG => ?_, fun o _ => ?_⟩
  · obtain ⟨g, hg⟩ := get_of_mem hG
    exact ⟨groupOkB_of (h.groups g G hg), fun r hr => rowInB_of (h.rows g G hg r hr)⟩
  · split
    · rename_i x hx
      exact List.all_eq_true.2 fun r hr => rowInB_of (h.samples o x hx r hr)
    · rfl

theorem inOrderB_iff : inOrderB S = true ↔ InOrder S := ⟨inOrder_of, inOrderB_of⟩

theorem openKindsB_of (h : OpenKinds S) : openKindsB S = true := by
  unfold openKindsB
  simp only [List.all_eq_true, bne_iff_ne, ne_eq]
  intro G hG r hr
  obtain ⟨g, hg⟩ := get_of_mem hG
  exact h g G hg r hr

theorem openKindsB_iff : openKindsB S = true ↔ OpenKinds S := ⟨openKinds_of, openKindsB_of⟩

theorem noneYetB_of (h : NoneYet S) : noneYetB S = true := by
  unfold noneYetB
  simp only [List.all_eq_true, Bool.or_eq_true, Array.isEmpty_iff]
  intro x hx
  obtain ⟨o, ho⟩ := get_of_mem hx
  cases hs : x.sampled with
  | true => exact Or.inl rfl
  | false => exact Or.inr (h o x ho hs)

theorem noneYetB_iff : noneYetB S = true ↔ NoneYet S := ⟨noneYet_of, noneYetB_of⟩

theorem sampledMembersB_of (h : SampledMembers S) : sampledMembersB S = true := by
  unfold sampledMembersB
  simp only [List.all_eq_true]
  intro G hG o ho
  obtain ⟨g, hg⟩ := get_of_mem hG
  obtain ⟨x, hx, hs⟩ := h g G hg o ho
  rw [hx]
  exact hs

theorem sampledMembersB_iff : sampledMembersB S = true ↔ SampledMembers S :=
  ⟨sampledMembers_of, sampledMembersB_of⟩

/-- The test of three says yes exactly where the three invariants hold. -/
theorem tidyB_iff : tidyB S = true ↔ InOrder S ∧ OpenKinds S ∧ NoneYet S := by
  refine ⟨tidy_gives, fun h => ?_⟩
  unfold tidyB
  simp only [Bool.and_eq_true]
  exact ⟨⟨inOrderB_of h.1, openKindsB_of h.2.1⟩, noneYetB_of h.2.2⟩

/-- All four tests. -/
def tidy4B (S : Statement) : Bool := tidyB S && sampledMembersB S

/-- **All four tests say yes exactly where the statement is tidy.** -/
theorem tidy4B_iff : tidy4B S = true ↔ Tidy S := by
  unfold tidy4B
  rw [Bool.and_eq_true, tidyB_iff, sampledMembersB_iff]
  exact ⟨fun h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩,
    fun h => ⟨⟨h.inOrder, h.kinds, h.noneYet⟩, h.members⟩⟩

end OnBytes.Means

