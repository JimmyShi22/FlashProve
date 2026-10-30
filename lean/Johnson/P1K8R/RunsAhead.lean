-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/RunsAhead.lean: A CLOSED FACT ON THE TABLE OF JOINTS' MAP OF NAMES (runsOf,
Johnson/Desc/First/Borders.lean; runsAt, Johnson/Desc/Sound/BordersForms.lean): the run
"K8.equations" stands under ONE name of the table alone: (5 + the sort's shift, "small").
  runsOf_k8        at every sort of segment, piece k and name r: a pair of runsOf sub k r whose run is "K8.equations" stands under k = 5 + shift sub and r = "small".
  runs_not_ahead   at the written list of segments, l ≤ 24: no run that the table names at a piece of segment l in front of the draw's is the run of which the composed meaning says that its forms may name what is ahead (MgData.ah, Johnson/Desc/Sound/MgAll.lean).
LIMITS. A fact on written lists. No soundness.
-/
import Johnson.P1K8R.TableAtK8
import Johnson.Desc.Sound.MgAt.Runs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart runsOf shift)

/-- The run "K8.equations" stands under one name of the table alone. -/
theorem runsOf_k8 (sub : ModelPart) (k : ℕ) (r : String) (p : ℕ × String) (hp : p ∈ runsOf sub k r)
    (he : p.2 = "K8.equations") : (k == 5 + shift sub && r == "small") = true := by
  obtain ⟨a, b⟩ := p
  have he' : b = "K8.equations" := he
  subst he'
  unfold runsOf at hp
  cases sub <;> simp only [] at hp <;> split_ifs at hp <;> simp_all

/-- A closed fact: the draw's piece in segment l is 5 + the sort's shift. -/
theorem k8PieceB_full : ((List.range 25).all fun l =>
    (linksFull[l]?).any fun sub => pcOf l == 5 + shift sub) = true := by decide

/-- **No run that the table names at a piece in front of the draw's may name what is ahead.** -/
theorem runs_not_ahead {l : ℕ} (hl : l ≤ 24) (k : ℕ) (r : String) (hk : k < pcOf l)
    (p : ℕ × String)
    (hp : p ∈ runsAt linksFull l k r) : (p.2 == "K8.equations") = false := by
  have h := List.all_eq_true.1 k8PieceB_full l (List.mem_range.2 (Nat.lt_succ_of_le hl))
  cases hs : linksFull[l]? with
  | none => simp [hs] at h
  | some sub =>
    simp only [hs, Option.any_some, beq_iff_eq] at h
    rw [runsAt_of linksFull l sub hs k r] at hp
    by_contra hc
    have he : p.2 = "K8.equations" := by simpa using hc
    have h2 := runsOf_k8 sub k r p hp he
    rw [← h] at h2
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact absurd h2.1 (Nat.ne_of_lt hk)

end P1K8T

#print axioms P1K8T.runs_not_ahead
