-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/GuardPlanDigits.lean: kind K5: at an attention link the parameters of the
lookup ON THE DIGITS fix the plan's own record f9 as their shape: the digits' twin of the first
clause of guard_theorems (Johnson/Desc/First/Att/GuardPlan.lean), which says the like of the lookup
on the calls.

Main names:
  `place_att_digits`: the place that lookAt returns at link 2 g + 1 for the digits holds the plan's
    tail's own two calls, numbers of padding keys, cap and record. By lookAt's own text
    (Johnson/Desc/First/Look/LookAt.lean).
  `digits_shape`: **under PlanIs: (Look.P.ofPlace set true xd).shape = some a.seam.tl.f9.** From the
    library's laws at the planner's return: Fo.ZPlan.planA_from
    (OnBytes/Tie/Pv/Lookup/Ends/FoZPlaced1.lean) and Fo.ZPlan.shapeZ_from (FoShapeZ.lean), and the
    lookups' shape_of_made.
No test is asked. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.GuardPlan
import OnBytes.Tie.Pv.Lookup.Ends.FoShapeZ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (lookAt shape_of_made)

/-- The digits' place at an attention link holds the plan's tail's own. -/
theorem place_att_digits {W : Verify.Public} {g : ℕ} {a : Attention.Plan}
    {xd : VerifiableInference.Desc.First.Look.Place} (h4 : W.p4 = true) (ha : W.A[g]? = some a)
    (hx : lookAt W (2 * g + 1) true = some xd) :
    xd.calls = #[a.seam.tl.z1.call, a.seam.tl.z2.call] ∧ xd.pub = a.seam.tl.f9.pub ∧
      xd.lid = a.seam.tl.lidb ∧ xd.fs = a.seam.tl.f9 := by
  have hn : ((2 * g + 1 == 2 * W.NGr) = false) := by
    rw [beq_eq_false_iff_ne]
    omega
  have h0 : (((2 * g + 1) % 2 == 0) = false) := by
    rw [beq_eq_false_iff_ne]
    omega
  have eg : (2 * g + 1) / 2 = g := by omega
  unfold lookAt at hx
  simp only [h4, if_true, hn, h0, eg, ha, Option.bind_some, Bool.false_eq_true, if_false] at hx
  obtain ⟨nx, -, rfl⟩ := Option.map_eq_some_iff.1 hx
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **The digits' parameters fix the plan's own record as their shape.** -/
theorem digits_shape {W : Verify.Public} (hP : PlanIs W) (h4 : W.p4 = true) {g : ℕ}
    {a : Attention.Plan} (ha : W.A[g]? = some a)
    {xd : VerifiableInference.Desc.First.Look.Place} (hx : lookAt W (2 * g + 1) true = some xd)
    (set : Params.Setting) :
    (VerifiableInference.Desc.First.Look.P.ofPlace set true xd).shape = some a.seam.tl.f9 := by
  obtain ⟨e1, e2, e3, e4⟩ := place_att_digits h4 ha hx
  obtain ⟨A0, pf, hA, e⟩ := hP g a ha
  have hZ : _root_.Fo.ZPlan.ShapeZ A0.seam.tl :=
    _root_.Fo.ZPlan.shapeZ_from (_root_.Fo.ZPlan.planA_from _ _ _ A0 hA)
  subst e
  rw [← e4]
  refine shape_of_made (p := VerifiableInference.Desc.First.Look.P.ofPlace set true xd) ?_
  show _root_.Fo.ShapeOf xd.calls xd.pub xd.lid xd.fs
  rw [e1, e2, e3, e4]
  exact hZ

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.place_att_digits
#print axioms VerifiableInference.Desc.First.Att.P.digits_shape
