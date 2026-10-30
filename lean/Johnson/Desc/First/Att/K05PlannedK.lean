-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05PlannedK.lean: KIND K5: the planned number of columns of the array of the reads (plannedK A, Johnson/Desc/First/Att/K05PublicB.lean) IS the plan's nW, at every A with OfPlan A
(Johnson/Desc/First/Att/Claims/OfPlan.lean), so at every attention plan of a public record with PlanIs. One theorem and a corollary. So the item "K5.readsThere", whose first clause says T.K = nW of the live
ledger's array, gives T.K = plannedK A. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.Claims.OfPlan
import Johnson.Desc.First.Att.K05PublicB
import Johnson.Desc.First.Att.GuardPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open K5Law (OfPlan ofPlan_u3_tree)

theorem plannedK_of_plan {A : Attention.Plan} (h : OfPlan A) : plannedK A = A.nW := by
  obtain ⟨_, T, hT, _, hK, _⟩ := ofPlan_u3_tree h
  unfold plannedK
  rw [hT]
  exact hK

theorem plannedK_of_planIs {W : Verify.Public} (hW : PlanIs W) {g : ℕ} {a : Attention.Plan} (ha : W.A[g]? = some a) :
    plannedK a = a.nW := by
  obtain ⟨A0, pf, h0, e⟩ := hW g a ha
  exact plannedK_of_plan ⟨_, _, _, A0, pf, h0, e⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.plannedK_of_plan
#print axioms VerifiableInference.Desc.First.Att.P.plannedK_of_planIs
