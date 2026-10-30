-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawFront.lean: THE SMALLNESS TEST: A YES OF `frontB`
(Johnson/Desc/First/K8/Front.lean) PAYS, AT THE STATE'S OWN VALUE, EVERY PREMISE AND CONDITION OF
THE LAW THAT READS THE SMALLNESS TEST'S PART OF THE VERIFIER'S STATE ALONE.

  `sameLay_own`: where tl is the state's own value, the law's condition "the state's value has the
    public value's layout" (`SameLay (recOf tl s) tl`) holds by the make.
  `front_spec`: what a yes says, clause by clause.
  `cond_of_front`: **a yes gives: a value tl is there; `SameLay (recOf tl s) tl`; `Extra s`; tl.NM ≤
    tl.gtTree.size; a third vector of reads**: the second half of the condition in front of
    `k08_rowT` (Johnson/Desc/First/K8/LawTable.lean) and its premises hgt and hu, at tl0 := tl.
  `frontB_of_tests`: the test says yes where the state's value has the seven fields of a value tlP
    that passes `planFitsB`, and `onThirdB` says yes.
  `frontB_none`: the test says no where no link is open.
Statements and proofs.
Limits. That the test says yes anywhere is not shown here. Nothing on soundness.

-/
import Johnson.Desc.First.K8.Front
import Johnson.Desc.First.K8.LawPlanFits
import Johnson.Desc.First.K8.LawLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Ready

open OnBytes OnBytes.Model

/-- At the state's own value the layouts are one. -/
theorem sameLay_own {s : S} {tl : HTailF2} (ht : s.tl? = some tl) : SameLay (recOf tl s) tl := by
  unfold recOf
  rw [ht]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- What a yes says. -/
theorem front_spec {s : S} (h : frontB s = true) :
    ∃ tl, s.tl? = some tl ∧ tl.funClosed = true ∧ (∀ Fn ∈ tl.funs.toList, Fn.tree = 2) ∧
      planFitsB tl = true := by
  unfold frontB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h3, hc⟩ := onThirdB_iff.1 h.1
  cases ht : s.tl? with
  | none => simp [onThird, ht] at h3
  | some tl =>
    refine ⟨tl, rfl, ?_, ?_, ?_⟩
    · simpa [closedNow, ht] using hc
    · intro Fn hFn
      have h4 : (tl.funs.toList.all fun Fn => Fn.tree == 2) = true := by
        simpa [onThird, ht] using h3
      simpa using List.all_eq_true.1 h4 Fn hFn
    · simpa [ht] using h.2

/-- **What the law reads of the state's own value.** -/
theorem cond_of_front {s : S} (h : frontB s = true) :
    ∃ tl, s.tl? = some tl ∧ SameLay (recOf tl s) tl ∧ Extra s ∧ tl.NM ≤ tl.gtTree.size ∧
      ∃ t, tl.ix.U[2]? = some (some t) := by
  obtain ⟨tl, ht, _, h3, hp⟩ := front_spec h
  obtain ⟨hF, hgt, hu⟩ := planFits_spec hp
  refine ⟨tl, ht, sameLay_own ht, fun t' ht' => ?_, hgt, hu⟩
  obtain rfl := Option.some.inj (ht.symm.trans ht')
  exact ⟨hF, h3⟩

/-- From the two elder tests and the test on a public value with the same seven fields. -/
theorem frontB_of_tests {tlP : HTailF2} {s : S} (h7 : lay7B tlP s = true)
    (hp : planFitsB tlP = true) (h3 : onThirdB s = true) : frontB s = true := by
  have e := lay7_of_test h7
  unfold lay7 at e
  cases ht : s.tl? with
  | none => simp [ht] at e
  | some tl =>
    rw [ht] at e
    have e' : planFitsB tl = true := (planFitsB_of_seven (Option.some.inj e)).trans hp
    unfold frontB
    rw [h3, ht]
    simp [e']

/-- Where no link is open the test says no. -/
theorem frontB_none {s : S} (h : s.tl? = none) : frontB s = false := by
  simp [frontB, h]

end VerifiableInference.Desc.First.K8.Ready

#print axioms VerifiableInference.Desc.First.K8.Ready.sameLay_own
#print axioms VerifiableInference.Desc.First.K8.Ready.front_spec
#print axioms VerifiableInference.Desc.First.K8.Ready.cond_of_front
#print axioms VerifiableInference.Desc.First.K8.Ready.frontB_of_tests
#print axioms VerifiableInference.Desc.First.K8.Ready.frontB_none
