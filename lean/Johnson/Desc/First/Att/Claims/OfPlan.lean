-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Claims/OfPlan.lean: kind K5: one name, OfPlan, for "what Attention.plan
returns, but for the field plFor of its record of the smallness test", and the plan's facts that the
kind's instance of the planes' law reads, at every plan of that sort.

Why. The attention plans of a record that Verify.publicOf returns are returns of Attention.plan but
for one field: behind the plans publicOf lays, in each plan's record of the smallness test, who owns
the one array that the sub-proof reads of another (the field plFor). The library has that as a
theorem: Fo.PubA.public_A_plFor (OnBytes/Tie/Pv/Lookup/Ends/FoPublicAPlFor.lean). That the field
does differ (an owner stands in it, and a return of Attention.plan bears none) is by reading and by
a run at the library's two written policies: no theorem. A text that is seated at the public record
runs at X.A[g]. So a theorem that takes "Attention.plan … = .ok A" as a premise, with the same A in
such a text's place, cannot be called there. The theorems of
Johnson/Desc/First/Att/Claims/PlanesHostTie.lean [not in this library] and
OpenedU3.lean [not in this library] take OfPlan A instead.

IS IT EMPTY HERE? `public_ofPlan` has two premises: a return of publicOf, and a plan at number g.
That publicOf returns is not shown here (by a run it returns at the library's two written policies,
with 12 and 2 attention plans). OfPlan has members wherever Attention.plan returns (`ofPlan_self`).

Main names:
  `OfPlan A`: there are settings, j, cf, A0 and pf with Attention.plan settings j cf = .ok A0 and
    A = A0 with pf as the field plFor of A0.seam.tl.
  `ofPlan_self`: the planner's return is OfPlan.
  `public_ofPlan`: Verify.publicOf pol KL layout = .ok X → X.A[g]? = some a → OfPlan a. A corollary
    of Fo.PubA.public_A_plFor, which says more: it names the settings, j and cf.
  `ofPlan_u3_tree`, `ofPlan_U`, `ofPlan_nm`, `ofPlan_shape`, `ofPlan_rows`: plan_u3_tree, plan_U,
    plan_nm (Johnson/Desc/First/Att/Claims/PlanU3.lean), plan_shape (Johnson/Road/Lane5AttPlan.lean)
    and bA_rows (Johnson/Desc/First/Att/Claims/PlanesHost.lean) at every A with OfPlan A.
Beside it: glue_plan_A (Johnson/Goal/Meaning/PlanOwn.lean) gives, of a member of X.A, the shape and
the own rounds' sizes of a plan that Attention.plan has made.

Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicAPlFor
import Johnson.Desc.First.Att.Claims.PlanU3
import Johnson.Desc.First.Att.Claims.PlanesHost

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model
/-- **A is what Attention.plan returns, but for the readers' records of shared matrices in its
record of the smallness test.** -/
def OfPlan (A : Attention.Plan) : Prop :=
  ∃ (settings : Model.Settings) (j : Attention.In) (cf : Attention.Cfg) (A0 : Attention.Plan)
    (pf : Array PlaceF), Attention.plan settings j cf = Except.ok A0 ∧
      A = { A0 with seam := { A0.seam with tl := { A0.seam.tl with plFor := pf } } }

theorem ofPlan_self {settings : Model.Settings} {j : Attention.In} {cf : Attention.Cfg}
    {A : Attention.Plan} (h : Attention.plan settings j cf = Except.ok A) : OfPlan A :=
  ⟨settings, j, cf, A, A.seam.tl.plFor, h, rfl⟩

/-- **Every attention plan of the public record is OfPlan.** -/
theorem public_ofPlan {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (a : Attention.Plan)
    (hg : X.A[g]? = some a) : OfPlan a := by
  obtain ⟨a0, h0, e⟩ := Fo.PubA.public_A_plFor h g a hg
  exact ⟨_, _, _, a0, a.seam.tl.plFor, h0, e⟩

theorem ofPlan_u3_tree {A : Attention.Plan} (h : OfPlan A) :
    A.iU3 = 0 ∧ ∃ T : HTree, A.seam.Fp.trees[A.iU3]? = some T ∧ T.R = 1 ∧ T.K = A.nW ∧
      T.rows.size = 1 := by
  obtain ⟨_, _, _, A0, pf, h0, rfl⟩ := h
  exact plan_u3_tree (A := A0) h0

theorem ofPlan_U {A : Attention.Plan} (h : OfPlan A) :
    A.seam.tl.ix.U = #[none, none, some 0, none] := by
  obtain ⟨_, _, _, A0, pf, h0, rfl⟩ := h
  exact plan_U (A := A0) h0

theorem ofPlan_nm {A : Attention.Plan} (h : OfPlan A) : A.seam.tl.NM = A.S.cf.NAs + 4 := by
  obtain ⟨_, _, _, A0, pf, h0, rfl⟩ := h
  exact plan_nm (A := A0) h0

theorem ofPlan_shape {A : Attention.Plan} (h : OfPlan A) :
    ∃ lid cf, Attention.shapeHid lid cf = Except.ok (A.S, A.fs) := by
  obtain ⟨st, _, cf, A0, pf, h0, rfl⟩ := h
  exact ⟨st.lidb, cf, (OnBytes.Road.L5.plan_shape h0).1⟩

theorem ofPlan_rows {A : Attention.Plan} (h : OfPlan A) :
    (A.seam.tl.mats.getD (A.S.cf.NAs + 2) {}).m = 2 ^ A.S.cf.lmb := by
  obtain ⟨_, _, _, A0, pf, h0, rfl⟩ := h
  exact bA_rows (X := A0) h0

end K5Law

#print axioms K5Law.ofPlan_self
#print axioms K5Law.public_ofPlan
#print axioms K5Law.ofPlan_u3_tree
#print axioms K5Law.ofPlan_U
#print axioms K5Law.ofPlan_nm
#print axioms K5Law.ofPlan_shape
#print axioms K5Law.ofPlan_rows
