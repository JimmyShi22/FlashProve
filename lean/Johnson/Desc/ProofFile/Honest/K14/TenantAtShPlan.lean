-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K14/TenantAtShPlan.lean: kind K14: at the full size no two of the
shared chain's three sampled messages have one tenant in the table of numbers that the soundness
side names Desc.K14.Law.Sh.nums (Johnson/Desc/K14/Law/SharedConst.lean), at the plan
P5J.AtMg.shPlan (Johnson/P5J/FreeShared.lean) and at every value of that table's open letters. One
statement: a call of tenant_at_head (Honest/K14/TenantAtHead.lean), whose head says what a tenant is
and where the sentence is asked (the field "tenant" of K14Asks, Honest/K14/Asks.lean).

  tenant_shNums   Function.Injective (Sh.nums h.shPlan O).tenant, at every O

Why it is a call. Sh.nums lays the first chain's two tenants into the table numbersSh at the plan's
first tree and two layouts of trees; the three tenants of the shared chain's own messages are
numbersSh's; and the plan h.shPlan is by its definition the plan of IM.Seats.nsA.

Kin. By unfolding it is tenant_tied h O.N₁ (Honest/K14/TenantAtHead.lean). P5J.freeOf_nums
(Johnson/P5J/FreeShared.lean) has the equation of tiedNumbers (At.N Zp cF) … with
Sh.nums h.shPlan (h.shOpen 𝔇₀).

Limits. Those of Honest/K14/TenantAtHead.lean: the premise h is a hypothesis.

This file proves nothing about soundness, completeness, hiding or any other property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.K14.TenantAtHead
import Johnson.P5J.FreeShared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Chain)

/-- **At the full size, at the table of the shared chain's numbers that the soundness side names
Sh.nums: no two of the three messages have one tenant.** -/
theorem tenant_shNums {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    (h : P5J.AtMg o Z D r Zp Np cF) {P₀ P₁ Cells Tok : Type}
    (O : _root_.Desc.K14.Law.ShOpen P₀ P₁ Cells Tok h.shPlan.Q) :
    Function.Injective (_root_.Desc.K14.Law.Sh.nums h.shPlan O).tenant :=
  tenant_at_head h rfl

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.tenant_shNums
