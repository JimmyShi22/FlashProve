-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P1K2R/K5AtConst.lean: code switching (K2): THE NAMED TEST k5PlanB AT THE TERMS AT
WHICH
K2's LAST LINE ASKS IT (k2Cond_tests, Johnson/P1K2R/LastLineTests.lean: its premise hK5):
FROM THE HEAD, WITH ITS ENTRY TESTS (it calls pins_of_laid).
  mem_attW     m < 23 and IM.subW (m + 1) = .attention put m + 1 among the written attention links
  hK5_head     ∀ m, m < 23 → IM.subW (m + 1) = .attention →
               k5PlanB Zp (dC Hd).pubD.d5 Zp.first.layout (m + 1) = true
BY CALLS: k5PlanB_head (Johnson/P1K2R/K5PlanCut.lean: k5PlanB is k5RestB under the head and
AtWritten) · k5RestB_in_scope (Johnson/P1K2R/K5RestScope.lean) · at_written at pins_of_laid.
LIMITS. Joins. A member of the head is proved at storedPublicFiles and zGap alone (at secondHashFunction; side library
AtFullSide/Top/). No soundness is claimed.
-/
import Johnson.P1K2R.K5RestScope
import Johnson.P1K2R.ThirdAtConst

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P1K2 (k5PlanB attW)

variable {Z : VerifierAndGoals.PublicFiles} {Dw : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem mem_attW {m : ℕ} (hm : m < 23) (ha : IM.subW (m + 1) = .attention) : m + 1 ∈ attW := by
  unfold attW
  exact List.mem_filter.2 ⟨List.mem_range'_1.2 ⟨by omega, by omega⟩, decide_eq_true ha⟩

/-- **k2Cond_tests' premise hK5, under the head alone.** -/
theorem hK5_head (Hd : P5J.AtMgA OnBytes.secondHashFunction Z Dw r₀ Zp Np cF x) :
    ∀ m, m < 23 → IM.subW (m + 1) = .attention →
      k5PlanB Zp (dC Hd).pubD.d5 Zp.first.layout (m + 1) = true := by
  intro m hm ha
  rw [P1K2.k5PlanB_head Hd.toAtMg Hd.𝔇
    (K2Ties.at_written Hd.scope Hd.laid (P5J.pins_of_laid Hd.scope Hd.laid).1) Zp.first.layout
    (mem_attW hm ha)]
  exact P1K2.k5RestB_in_scope Hd.scope Hd.laid (mem_attW hm ha)

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.mem_attW
#print axioms VerifiableInference.Desc.First.K2Caller.hK5_head
