-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/GuardPublic.lean: kind K5: AT A RETURN OF Verify.publicOf THE STORED
ATTENTION PLAN IS, BUT FOR ONE FIELD, WHAT THE PLANNER RETURNS AT THAT PLAN's OWN SETTINGS, INPUT
AND CONFIGURATION: so "plan" and "own" of K5Public are theorems there: no test need ask them, and
the planner need not be run anew.

Main names:
  `plan_at_own`: Attention.plan s j cf = .ok A0 → Attention.plan A0.settings A0.inp A0.S.cf = .ok
    A0.
  `public_plan`: **Verify.publicOf pol KL layout = .ok X → X.A[g]? = some a → ∃ A0 pf,
    Attention.plan a.settings a.inp a.S.cf = .ok A0 ∧ a = A0 with pf as the field plFor of
    A0.seam.tl.** Over the library's public_A_plFor
    (OnBytes/Tie/Pv/Lookup/Ends/FoPublicAPlFor.lean), which names the planner's three arguments off
    the public record; here they are read off a itself.
The library's lemmas that are called, not typed anew: planA_shapeHid (the return holds the settings;
OnBytes/Tie/Pv/Lookup/Ends/FoMadePublic.lean), plan_shape (the input;
Johnson/Road/Lane5AttPlan.lean), shaped_of_hid (the configuration). Looked for and not found in the
library: plan_at_own's like (searched: the theorems of the 31 files that name Attention.plan, for
"settings ="). Beside it: Johnson/Goal/Meaning/PlanOwn.lean has the like for two fields (a.S
and a.own are those of a return of the planner, the settings, input and configuration under "there
are").
  `PlanIs W`, `planIs_public`: what the laws spend of it, as a statement on a public record W; it
    holds at every return of publicOf. WHY A STATEMENT OF ITS OWN: a description may make its public
    record by another text than publicOf (publicOf's text with a letter in the second hash
    function's place): that letter reaches the tests on the tables' digests and the field digests,
    no plan; that PlanIs holds at such a record is not shown here.
Limits. That publicOf returns is a premise. Nothing on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicAPlFor
import OnBytes.Tie.Pv.Lookup.Ends.FoMadePublic
import Johnson.Road.Lane5AttPlan
import Johnson.Road.Lane5AttCallsH

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open OnBytes.Road.L5 (plan_shape shaped_of_hid)

/-- The planner returns the same at its return's own settings, input and configuration. -/
theorem plan_at_own {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg}
    {A0 : Attention.Plan} (h : Attention.plan settings i cf = Except.ok A0) :
    Attention.plan A0.settings A0.inp A0.S.cf = Except.ok A0 := by
  rw [(Fo.Pub.planA_shapeHid _ _ _ _ h).2, (plan_shape h).2, (shaped_of_hid (plan_shape h).1).cfg]
  exact h

/-- **The stored plan at a return of publicOf.** -/
theorem public_plan {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (a : Attention.Plan)
    (hg : X.A[g]? = some a) :
    ∃ (A0 : Attention.Plan) (pf : Array PlaceF),
      Attention.plan a.settings a.inp a.S.cf = Except.ok A0 ∧
      a = { A0 with seam := { A0.seam with tl := { A0.seam.tl with plFor := pf } } } := by
  obtain ⟨A0, h0, e⟩ := Fo.PubA.public_A_plFor h g a hg
  have e1 : a.settings = A0.settings := by
    have t := congrArg Attention.Plan.settings e
    exact t
  have e2 : a.inp = A0.inp := by
    have t := congrArg Attention.Plan.inp e
    exact t
  have e3 : a.S = A0.S := by
    have t := congrArg Attention.Plan.S e
    exact t
  refine ⟨A0, a.seam.tl.plFor, ?_, e⟩
  rw [e1, e2, e3]
  exact plan_at_own h0

/-- **What the laws spend of "the public record is what publicOf returns"**: each stored attention
plan is, but for the field plFor of seam.tl, what the planner returns at that plan's own settings,
input and configuration. -/
def PlanIs (W : Verify.Public) : Prop :=
  ∀ (g : ℕ) (a : Attention.Plan), W.A[g]? = some a →
    ∃ (A0 : Attention.Plan) (pf : Array PlaceF),
      Attention.plan a.settings a.inp a.S.cf = Except.ok A0 ∧
      a = { A0 with seam := { A0.seam with tl := { A0.seam.tl with plFor := pf } } }

/-- It holds at every return of publicOf. -/
theorem planIs_public {pol KL : ByteArray} {layout : Option ByteArray} {W : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok W) : PlanIs W :=
  fun g a hg => public_plan h g a hg

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.planIs_public
#print axioms VerifiableInference.Desc.First.Att.P.plan_at_own
#print axioms VerifiableInference.Desc.First.Att.P.public_plan
