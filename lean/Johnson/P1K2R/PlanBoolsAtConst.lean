-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P1K2R/PlanBoolsAtConst.lean: code switching (K2): THE TWO NAMED TESTS linkPlanB ·
headPlanB AT THE TERMS AT WHICH K2's LAST LINE ASKS THEM (k2Cond_tests,
Johnson/P1K2R/LastLineTests.lean: its premises hLP · hHP): UNDER THE HEAD ALONE. AND THE TIE OF THE
TWO SPELLINGS, UNDER NAMES.
  pubD_nsOf    (dC Hd).pubD.nsOf = P5J.At.nsOf Zp: by the two texts (rfl)
  pubD_d3      (dC Hd).pubD.d3 = K3Data.of (P5J.At.X Zp) (P5J.At.sentAt Zp): by the two texts (rfl)
  hLP_head     ∀ m, m < 23 → linkPlanB Zp (dC Hd).pubD.nsOf (dC Hd).pubD.d3 (m + 1) = true
  hHP_head     headPlanB Zp (dC Hd).pubD.nsOf (dC Hd).pubD.d3 = true
BY CALLS: linkPlanB_in_scope | headPlanB_in_scope (Johnson/P1K2R/PlanBoolsScope.lean) at the head's
own scope and laid.
LIMITS. Joins. A member of the head is proved at storedPublicFiles and zGap alone (at secondHashFunction; side library
AtFullSide/Top/). k5PlanB is not here. No soundness is claimed.

-/
import Johnson.P1K2R.PlanBoolsScope
import Johnson.P1K2R.ThirdAtConst

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (K3Data)
open P1K2 (linkPlanB headPlanB)

variable {Z : VerifierAndGoals.PublicFiles} {Dw : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The two spellings of «the link's number of slots». -/
theorem pubD_nsOf (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) :
    (dC Hd).pubD.nsOf = P5J.At.nsOf Zp := rfl

/-- The two spellings of the lookups' public data. -/
theorem pubD_d3 (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) :
    (dC Hd).pubD.d3 = K3Data.of (P5J.At.X Zp) (P5J.At.sentAt Zp) := rfl

/-- **k2Cond_tests' premise hLP, under the head alone.** -/
theorem hLP_head (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) :
    ∀ m, m < 23 → linkPlanB Zp (dC Hd).pubD.nsOf (dC Hd).pubD.d3 (m + 1) = true := by
  intro m hm
  rw [pubD_nsOf, pubD_d3]
  exact P1K2.linkPlanB_in_scope Hd.scope Hd.laid (by omega)

/-- **k2Cond_tests' premise hHP, under the head alone.** -/
theorem hHP_head (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) :
    headPlanB Zp (dC Hd).pubD.nsOf (dC Hd).pubD.d3 = true := by
  rw [pubD_nsOf, pubD_d3]
  exact P1K2.headPlanB_in_scope Hd.scope Hd.laid

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.pubD_nsOf
#print axioms VerifiableInference.Desc.First.K2Caller.pubD_d3
#print axioms VerifiableInference.Desc.First.K2Caller.hLP_head
#print axioms VerifiableInference.Desc.First.K2Caller.hHP_head
