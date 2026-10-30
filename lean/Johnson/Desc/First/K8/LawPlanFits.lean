-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawPlanFits.lean: THE SMALLNESS TEST: WHAT A YES OF THE PUBLIC TEST
`planFitsB` (Johnson/Desc/First/K8/PlanFits.lean) GIVES, AT THE PLAN'S VALUE AND, WITH THE PUBLIC
ITEM "K8.lay7", AT THE VERIFIER'S STATE.

  `planFits_spec`: a yes gives the three premises of the law `k08_row_named`
    (Johnson/Desc/First/K8/LawNamedRow.lean) and of `cond_of_tests` that speak of the plan's value
    alone: the library's `Port.Fits`; as many numbers of symbol arrays as matrices; a third vector
    of reads.
  `planFitsB_of_seven`: the test reads fields of "K8.lay7" alone: two values with the same seven
    fields get one answer.
  `facts_of_tests`: **so, at a state s in which a link is open, with the tests `lay7B tlP s` and
    `planFitsB tlP`: the three facts hold of the state's own value.**
  `planFitsB_false`: the test can say no: at the structure's default values with one matrix
    declared.
Statements and proofs.
Limits. That the plan's values pass is shown nowhere here. Nothing on soundness.

-/
import Johnson.Desc.First.K8.PlanFits
import Johnson.Desc.First.K8.LawCondAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Ready

open OnBytes OnBytes.Model

/-- What a yes gives. -/
theorem planFits_spec {tl : HTailF2} (h : planFitsB tl = true) :
    OnBytes.Tie.Pv.Tail.Port.Fits tl ∧ tl.NM ≤ tl.gtTree.size ∧
      ∃ t, tl.ix.U[2]? = some (some t) := by
  unfold planFitsB at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨fun mu hmu => h1 mu hmu, h2, ?_⟩
  cases hu : tl.ix.U[2]? with
  | none => simp [hu] at h3
  | some x =>
    cases x with
    | none => simp [hu] at h3
    | some t => exact ⟨t, rfl⟩

/-- The test reads fields of the seven alone. -/
theorem planFitsB_of_seven {tl tlP : HTailF2} (h : seven tl = seven tlP) :
    planFitsB tl = planFitsB tlP := by
  simp only [seven, Prod.mk.injEq] at h
  obtain ⟨a1, a2, _, _, a5, a6, a7⟩ := h
  unfold planFitsB
  rw [a1, a2, a5, a6, a7]

/-- **At the verifier's state.** -/
theorem facts_of_tests {tlP tl : HTailF2} {s : S} (ht : s.tl? = some tl)
    (h7 : lay7B tlP s = true) (hp : planFitsB tlP = true) :
    OnBytes.Tie.Pv.Tail.Port.Fits tl ∧ tl.NM ≤ tl.gtTree.size ∧
      ∃ t, tl.ix.U[2]? = some (some t) := by
  have e := lay7_of_test h7
  unfold lay7 at e
  rw [ht] at e
  exact planFits_spec ((planFitsB_of_seven (Option.some.inj e)).trans hp)

/-- The test can say no. -/
theorem planFitsB_false : planFitsB ({ NM := 1 } : HTailF2) = false := by decide

end VerifiableInference.Desc.First.K8.Ready

#print axioms VerifiableInference.Desc.First.K8.Ready.planFits_spec
#print axioms VerifiableInference.Desc.First.K8.Ready.planFitsB_of_seven
#print axioms VerifiableInference.Desc.First.K8.Ready.facts_of_tests
#print axioms VerifiableInference.Desc.First.K8.Ready.planFitsB_false
