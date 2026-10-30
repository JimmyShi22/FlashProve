-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/PlanShp.lean: CONDITIONAL on the planner's return: at an attention plan
that the planner returns, the smallness test's part has one shape a matrix
(`seam.tl.shp.size = seam.tl.NM`), and its number of matrices is the length of its list
(`seam.tl.NM = seam.tl.mats.size`).

How. The planner lays that part by the routine that adds the trees
(`HTailF2.addTreesF`, OnBytes/Model/Tail.lean), which makes the list of shapes by a map over the
numbers below the number of matrices. The library has that as a law on the routine's return
(`addTreesF_fits`, OnBytes/Tie/Pv/Tail/EndSame.lean). The walk through the planner's text up to the
routine's call follows the library's `K5Law.plan_nm`
(Johnson/Desc/First/Att/Claims/PlanU3.lean), line for line. The second fact: that lemma's number,
and the length of the planner's list (`plan_mats`, Johnson/Road/Lane5AttLabel.lean).

The library also has both as ONE test with code, evaluated true at its full example
(OnBytes/Tie/Pv/Plan/PlacePaid.lean, the test named "NM"): an evaluation at one example. Here they
are theorems at every return of the planner.

Main names:
  `hplan_of_plan`, `hNM_of_plan`: at what the planner returns.
  `hplan_ofPlan`, `hNM_ofPlan`: at a plan that is the planner's but for one field (`K5Law.OfPlan`).
  `hplan_at_head`, `hNM_at_head`: under the library's one head on the public input, at the plan of
    each group.

Limits. The head is a hypothesis.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.Door.Law.K5RestPublic
import Johnson.Desc.First.Att.Claims.PlanU3
import Johnson.Road.Lane5AttLabel
import OnBytes.Tie.Pv.Tail.EndSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 Fo Fo.Pub Fo.ZPlan

/-- **One shape a matrix, at what the planner returns.** Conditional: the planner's return. -/
theorem hplan_of_plan {settings : Settings} {j : Attention.In} {cf : Attention.Cfg}
    {A : Attention.Plan} (h : Attention.plan settings j cf = .ok A) :
    A.seam.tl.shp.size = A.seam.tl.NM := by
  unfold Attention.plan at h
  obtain ⟨-, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨-, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨-, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨r, hr, h⟩ := OnBytes.Road.L5.bind_ok h
  obtain ⟨S, fs⟩ := r
  obtain ⟨-, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨seam0, -, h⟩ := OnBytes.Road.L5.bind_ok h
  obtain ⟨hn, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨-, h⟩ := OnBytes.Road.L5.jp_ok h
  obtain ⟨seam, h1, h⟩ := OnBytes.Road.L5.bind_ok h
  have e := Except.ok.inj h
  subst e
  obtain ⟨T, hA⟩ := seamPlan_cut h1
  show seam.tl.shp.size = seam.tl.NM
  exact (OnBytes.Tie.Pv.Tail.Port.addTreesF_fits _ _ _ _ _ _ _ _ _ _ hA).2.1

/-- **The number of matrices is the length of the list, at what the planner returns.**
Conditional: the planner's return. -/
theorem hNM_of_plan {settings : Settings} {j : Attention.In} {cf : Attention.Cfg}
    {A : Attention.Plan} (h : Attention.plan settings j cf = .ok A) :
    A.seam.tl.NM = A.seam.tl.mats.size := by
  rw [K5Law.plan_nm h, OnBytes.Road.L5.plan_mats h, Array.size_map]
  unfold Attention.matrices
  simp

/-- The first at a plan that is the planner's but for the readers' places of shared matrices. -/
theorem hplan_ofPlan {A : Attention.Plan} (h : K5Law.OfPlan A) :
    A.seam.tl.shp.size = A.seam.tl.NM := by
  obtain ⟨_, _, _, A0, pf, h0, rfl⟩ := h
  show A0.seam.tl.shp.size = A0.seam.tl.NM
  exact hplan_of_plan h0

/-- The second at such a plan. -/
theorem hNM_ofPlan {A : Attention.Plan} (h : K5Law.OfPlan A) :
    A.seam.tl.NM = A.seam.tl.mats.size := by
  obtain ⟨_, _, _, A0, pf, h0, rfl⟩ := h
  show A0.seam.tl.NM = A0.seam.tl.mats.size
  exact hNM_of_plan h0

end H2K5.Honest

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First
open P5J (AtMgA TS)
open H2K5.Door

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : Look.Place} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- **One shape a matrix, at the plan of each group, under the head.** Conditional: the head; ea:
the group's plan. -/
theorem hplan_at_head {g : ℕ} {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) :
    a.seam.tl.shp.size = a.seam.tl.NM := hplan_ofPlan (ofPlan_all h ea)

include h in
/-- **The number of matrices is the length of the list, at the plan of each group, under the
head.** Conditional: the head; ea: the group's plan. -/
theorem hNM_at_head {g : ℕ} {a : Attention.Plan} (ea : (P5J.At.X Zp).A[g]? = some a) :
    a.seam.tl.NM = a.seam.tl.mats.size := hNM_ofPlan (ofPlan_all h ea)

end H2K5.Honest

#print axioms H2K5.Honest.hplan_of_plan
#print axioms H2K5.Honest.hNM_of_plan
#print axioms H2K5.Honest.hplan_ofPlan
#print axioms H2K5.Honest.hNM_ofPlan
#print axioms H2K5.Honest.hplan_at_head
#print axioms H2K5.Honest.hNM_at_head
