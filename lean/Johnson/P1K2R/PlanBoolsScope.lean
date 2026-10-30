-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/PlanBoolsScope.lean: code switching (K2): TWO OF THE NAMED TESTS ON THE
PLANNER's OUTPUT ARE THEOREMS IN SCOPE, WHERE THE VALUE IS LAID: linkPlanB at the links 0 … 23 and
headPlanB (Johnson/P1K2R/PlanBools.lean), at the closed constant's letters (P5J.At,
Johnson/P5J/LettersAt.lean). NO PIN · NO VALUE · NO DECISION
OF LEAN's KERNEL.
  linkPlanB_in_scope   (hZ : VerifierAndGoals.InScope Z = true) (L : P5J.LaidAt …) (hl : l < 24) :
               linkPlanB Zp (At.nsOf Zp) (K3Data.of (At.X Zp) (At.sentAt Zp)) l = true
  headPlanB_in_scope   the like for headPlanB
BY CALLS ALONE: linkPlanB_of_built | headPlanB_of_built (Johnson/P1K2R/PlanNumbers.lean) ·
built_link_at | built_head_at | public_at_laid (Johnson/P1K2R/BuiltLinkAt.lean) ·
«nothing is heard»: Fo.ZPlan.public_heard (Johnson/Desc/First/Look/HeardNone.lean: a law of the
planner's text) · inScope_readFiles (StageSizesAtScope.lean) · LaidAt's own opened | planOk.
LIMITS. Joins. hZ and LaidAt are not shown met: no example. k5PlanB and headUnheardB are not here.
No soundness is claimed.
-/
import Johnson.P1K2R.PlanNumbers
import Johnson.P1K2R.BuiltLinkAt
import Johnson.Desc.First.Look.HeardNone

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (K3Data)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- **linkPlanB IS A THEOREM IN SCOPE.** -/
theorem linkPlanB_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {l : ℕ} (hl : l < 24) :
    linkPlanB Zp (P5J.At.nsOf Zp) (K3Data.of (P5J.At.X Zp) (P5J.At.sentAt Zp)) l = true := by
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hZ
  obtain ⟨Bs, base, O⟩ := L.opened
  obtain ⟨uG, uA, -⟩ := Fo.ZPlan.public_heard (public_at_laid L)
  obtain ⟨X, hX, -, hg, arms⟩ := built_link_at hZ L hl
  refine linkPlanB_of_built hZ hR O L.planOk hl hX hg ?_
  rcases arms with ⟨he, hk, a, hA, n1, f1⟩ | ⟨he, hk, hp, hG, n1, f1⟩
  · exact Or.inl ⟨he, hk, a, hA, n1, f1, uA _ a hA⟩
  · exact Or.inr ⟨he, hk, hp, hG, n1, f1, uG _ hp hG⟩

/-- **headPlanB IS A THEOREM IN SCOPE.** -/
theorem headPlanB_in_scope (hZ : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) :
    headPlanB Zp (P5J.At.nsOf Zp) (K3Data.of (P5J.At.X Zp) (P5J.At.sentAt Zp)) = true := by
  obtain ⟨pp, hR⟩ := H2K.Sizes.inScope_readFiles hZ
  obtain ⟨Bs, base, O⟩ := L.opened
  obtain ⟨b, hb, -, -, hns, -⟩ := built_head_at hZ L
  exact headPlanB_of_built hZ hR O L.planOk hb hns

end P1K2

#print axioms P1K2.linkPlanB_in_scope
#print axioms P1K2.headPlanB_in_scope
