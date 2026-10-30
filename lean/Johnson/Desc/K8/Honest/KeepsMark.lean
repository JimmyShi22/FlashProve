-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/KeepsMark.lean: THE SMALLNESS TEST: WHAT THE STEP OF THE KIND's OWN MEMBER
LEAVES (`K8Keeps`, Johnson/Desc/K8/Honest/Keeps.lean), WITH "NO MARK STANDS BEHIND" INSIDE THE
CLAUSE; ITS PAYER FROM THE WHOLE MEMBER's ACCEPTING STEP (`StepYes`,
Johnson/Top/H0/Walk/Reach.lean); AND WHAT THE CLAUSE LEAVES OF THE SEGMENT's OWN PART OF THE STATE.
Lemmas on the verifier's own text; none of the library's goals.

  `K8KeepsM s s'`   `K8Keeps s s'`, and no mark stands at s'. It names no place's numbers: the
                   clause has no public parameter
  **`keepsM_of_step`**   THE PAYER: at any block that is seated over the draw's block (`Seats blk
                   (approximateRangeProofDrawKind atS p)`, Johnson/Desc/First/K8/LawSeated.lean): StepYes ft blk s s' →
                   K8KeepsM s s'
  `K8KeepsM.rest`   the chain's statement and what was put out are as they were
  `keeps_lay`, `keeps_att`, `keeps_head`   THE SEGMENT's OWN PART `here` IS NOT AS IT WAS: the
                   test's data lie inside it. It is as it was BUT FOR THESE DATA: at each of the
                   three sorts of segment: s.here = .head a → ∃ tl', s'.here = .head { a with tl :=
                   tl' }, and the like
NO DEVICE. TACTICS THAT SEARCH: `simp [a list]` on four lines, each on what `S.putTl` lays at one
sort of segment.
Limits. From a yes alone. That a description's member is seated over the draw's block is a premise.
Of the runs that the kind's block states (claims, after) nothing: they are run at later members.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.Keeps
import Johnson.Top.H0.Walk.ReachInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8
open Johnson.Desc.First.Walk.Tied (StepYes stepYes_decide)

/-- **What the draw's member leaves, with "no mark stands behind" inside.** -/
def K8KeepsM (s s' : S) : Prop := K8Keeps s s' ∧ s'.failed = none

/-- **The payer, from the whole member's accepting step.** -/
theorem keepsM_of_step {Cl : Type} {p : Par} {blk : Block S Cl} (hc : Seats blk (approximateRangeProofDrawKind atS p))
    {ft : Nat} {s s' : S} (h : StepYes ft blk s s') : K8KeepsM s s' := by
  obtain ⟨rs, gs, hd⟩ := stepYes_decide h
  exact keeps_of_seats hc hd

theorem K8KeepsM.rest {s s' : S} (h : K8KeepsM s s') : s'.st = s.st ∧ s'.out = s.out :=
  ⟨h.1.rest.1, h.1.rest.2.2.2.2.2.2.1⟩

/-- At a layers' segment. -/
theorem keeps_lay {s s' : S} (h : K8Keeps s s') {a : LayOwn} (ha : s.here = .lay a) :
    ∃ tl', s'.here = .lay { a with tl := tl' } := by
  obtain ⟨tl, cf, first, -, -, -, -, -, rfl⟩ := h
  exact ⟨{ tl with cfF := cf, cfFirst := first }, by simp [S.putTl, ha]⟩

/-- At an attention segment. -/
theorem keeps_att {s s' : S} (h : K8Keeps s s') {a : AttOwn} (ha : s.here = .att a) :
    ∃ tl', s'.here = .att { a with tl := tl' } := by
  obtain ⟨tl, cf, first, -, -, -, -, -, rfl⟩ := h
  exact ⟨{ tl with cfF := cf, cfFirst := first }, by simp [S.putTl, ha]⟩

/-- At the output head. -/
theorem keeps_head {s s' : S} (h : K8Keeps s s') {a : HeadOwn} (ha : s.here = .head a) :
    ∃ tl', s'.here = .head { a with tl := tl' } := by
  obtain ⟨tl, cf, first, -, -, -, -, -, rfl⟩ := h
  by_cases ho : a.opened = true
  · exact ⟨{ tl with cfF := cf, cfFirst := first }, by simp [S.putTl, ha, ho]⟩
  · have e : s.putTl { tl with cfF := cf, cfFirst := first } = s := by simp [S.putTl, ha, ho]
    exact ⟨a.tl, (congrArg S.here e).trans ha⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.keepsM_of_step
#print axioms VerifiableInference.Desc.First.K8.Honest.K8KeepsM.rest
#print axioms VerifiableInference.Desc.First.K8.Honest.keeps_lay
#print axioms VerifiableInference.Desc.First.K8.Honest.keeps_att
#print axioms VerifiableInference.Desc.First.K8.Honest.keeps_head
#print axioms VerifiableInference.Desc.First.K8.Honest.K8KeepsM
