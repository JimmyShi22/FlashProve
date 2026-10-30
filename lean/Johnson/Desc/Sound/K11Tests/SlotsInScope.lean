-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/K11Tests/SlotsInScope.lean: AT ALL PUBLIC FILES IN THE GOALS' SCOPE THE MERGE OF
THE CLAIMS ON THE COMMITTED TABLE (kind K11) HAS 3570 SLOTS; so at most 8192, which is the one
premise (hn) that inM_in_scope (Johnson/Desc/Sound/K11Tests/LettersSevenInScope.lean) leaves at that
kind's own number. Two joinings, by calls alone: no law is typed here, and nothing is evaluated.

  slots_in_scope   (K11.parOf Z G₀).nMsg = 3570
  slots_le         (K11.parOf Z G₀).nMsg ≤ 8192

THE LINKS, ALL LYING: the merge's number of slots is the output head's plan's (parOf_nMsg,
Johnson/Top/H0/MergeLaw/PlanNumsAt.lean) · HPlanH2.ns is by its definition the field nMsg
(OnBytes/Model/HeadPlan.lean) · in scope that number is 3570 (plan_in_scope's field ns,
Johnson/Desc/Kinds/Law/HeadPlanWritten.lean: the number is computed there).

lay and mk are general. No premise on the plain road's public part is spent.

Limits. That the premises can be met together is not shown here. The full size alone. Nothing on
soundness.

-/
import Johnson.Top.H0.MergeLaw.PlanNumsAt
import Johnson.Desc.Kinds.Law.HeadPlanWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LT28.K11Tests

open OnBytes.Model.Verify (publicOf)
open VerifiableInference.Desc.First.MergeLaw (parOf_nMsg)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (plan_in_scope)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {Z : ProofFile.Pub}
  {mk : ProofFile.LinksBy} {G₀ : ProofFile.Ground}

/-- **The merge has 3570 slots.** -/
theorem slots_in_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hX : publicOf P.pol P.KL lay = .ok Z.p.X) (hG : ProofFile.blankBy mk Z = some G₀) :
    (K11.parOf Z G₀).nMsg = 3570 :=
  (parOf_nMsg hG).trans (plan_in_scope hS hR hX).ns

/-- So at most 8192. -/
theorem slots_le (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hX : publicOf P.pol P.KL lay = .ok Z.p.X) (hG : ProofFile.blankBy mk Z = some G₀) :
    (K11.parOf Z G₀).nMsg ≤ 8192 := by
  rw [slots_in_scope hS hR hX hG]
  decide

end LT28.K11Tests

#print axioms LT28.K11Tests.slots_in_scope
#print axioms LT28.K11Tests.slots_le
