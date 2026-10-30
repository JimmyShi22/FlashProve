-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Means/TestsLaw.lean: each test of Johnson/Desc/Means/TestsB.lean gives the condition
that it stands for.

Main theorems: groupOk_of, rowIn_of, maskReady_of, layoutEq_of, layAt_gives, combineAt_gives.

What is not claimed. The converses. Nothing on where a run calls the tests.

-/
import Johnson.Desc.Means.Says
import Johnson.Desc.Means.TestsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

theorem nodup_of_distinct : ∀ l : List Nat, distinctNats l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    unfold distinctNats at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at h
    exact List.nodup_cons.2 ⟨h.1, nodup_of_distinct l h.2⟩

theorem groupOk_of {S : Statement} {G : Group} (h : groupOkB S G = true) : GroupOk S G := by
  unfold groupOkB at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨nodup_of_distinct _ h1, h2, h3, ?_, ?_⟩
  · intro o ho x hx
    have c := h4 o ho
    rw [hx] at c
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at c
    exact c.1
  · intro o ho x hx
    have c := h4 o ho
    rw [hx] at c
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at c
    exact c.2

theorem rowIn_of {S : Statement} {G : Group} {row : Row} (h : rowInB S G row = true) :
    RowIn S G row := by
  unfold rowInB at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, fun w hw => ⟨(h3 w hw).1.1, (h3 w hw).1.2, (h3 w hw).2⟩, h4⟩

theorem maskReady_of {L : GroupLayout} {acc : GroupRow} (h : maskReadyB L acc = true) :
    MaskReady L acc := by
  unfold maskReadyB at h
  simp only [Bool.or_eq_true, beq_iff_eq, Array.isEmpty_iff] at h
  exact h

theorem layoutEq_of {a b : GroupLayout} (h : layoutEqB a b = true) : a = b := by
  unfold layoutEqB at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  cases a
  cases b
  simp only at h1 h2 h3 h4 h5 h6 h7 h8
  subst h1 h2 h3 h4 h5 h6 h7 h8
  rfl

/-- The test at the laying gives the five conditions of the law of the laying. -/
theorem layAt_gives {S : Statement} {g : Nat} {row : Row} {acc : GroupRow}
    (h : layAt S g row acc = true) :
    ∃ G L, S.groups[g]? = some G ∧ S.layout g = some L ∧ GroupOk S G ∧ RowIn S G row ∧
      MaskReady L acc := by
  unfold layAt at h
  cases hG : S.groups[g]? with
  | none => simp [hG] at h
  | some G =>
    cases hL : S.layout g with
    | none => simp [hG, hL] at h
    | some L =>
      simp only [hG, hL, Bool.and_eq_true] at h
      exact ⟨G, L, rfl, rfl, groupOk_of h.1.1, rowIn_of h.1.2, maskReady_of h.2⟩

/-- The test at the batching gives the conditions of the law of the batching. -/
theorem combineAt_gives {S : Statement} {g : Nat} {input : RunInput}
    (h : combineAt S g input = true) :
    ∃ G, S.groups[g]? = some G ∧ S.layout g = some input.layout ∧ GroupOk S G ∧
      ∀ r ∈ input.rows.toList, RowIn S G r := by
  unfold combineAt combineFrameAt combineRowsAt at h
  cases hG : S.groups[g]? with
  | none => simp [hG] at h
  | some G =>
    cases hL : S.layout g with
    | none => simp [hG, hL] at h
    | some L =>
      simp only [hG, hL, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      refine ⟨G, rfl, by rw [layoutEq_of h2], groupOk_of h1, ?_⟩
      intro r hr
      have e : input.rows.toList.filter (rowInB S G) = input.rows.toList := by
        apply List.filter_eq_self.2
        have hl : (input.rows.toList.filter (rowInB S G)).length = input.rows.toList.length := by
          rw [h3, Array.length_toList]
        exact List.filter_eq_self.1 (List.length_filter_eq_length_iff.1 hl |> List.filter_eq_self.2)
      exact rowIn_of (List.filter_eq_self.1 e r hr)

end OnBytes.Means
