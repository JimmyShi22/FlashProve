-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Pub/JoinClaims.lean: CONDITIONAL: the field claims of HearPub
(Johnson/Desc/First/K4/Returns/Whole.lean), at every structure fo that the lookup can leave whose
calls' points have the plan's sizes, from the three tests of ClaimsB.lean.

Limits. The three tests are premises; none is evaluated here. No file of this folder proves the test
claimsB true at any plan. #guard is Lean's evaluator and gives no proof. This folder's tests
evaluate it at the small synthetic plan (ClaimsBTest.lean) alone. The other fields of HearPub are
not touched. No property is claimed.

  hearPub_claims   the field's own statement, written out.
  the example      says nothing as a statement: its end is one of its premises. It stands so that
                   Lean compares the type of hearPub_claims with the type of the field.
-/
import Johnson.Desc.First.K4.Returns.Whole
import Johnson.Desc.First.K4.Returns.Pub.ClaimsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.RtPub
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Desc.First.K4.Rt (HearPub)

/-- **The field claims of HearPub**, at every fo whose calls' points have the plan's sizes. -/
theorem hearPub_claims {P : Pub} {hp : HPlan2} {g : Nat} (hB : claimsB P hp g = true)
    (ht : tokensFit P g = true) (fo : Forest.Heard) (hz : zkFits P fo.zk = true) (iU3 : Nat)
    (tab : List TableAt) : ClaimsRet P hp g (Rt.envOf P hp g fo iU3 tab) :=
  claims_of_B hB rfl rfl hz ht

-- A comparison of two types when the file is compiled; as a statement it says nothing.
example {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {ztF : Array E} {iU3 : Nat}
    {tab : List TableAt} {laid : List (TableAsk × List (Nat × Nat))}
    (H : HearPub P hp g fo ztF iU3 tab laid) (hB : claimsB P hp g = true)
    (ht : tokensFit P g = true) (hz : zkFits P fo.zk = true) :
    HearPub P hp g fo ztF iU3 tab laid :=
  { H with claims := hearPub_claims hB ht fo hz iU3 tab }

end OnBytes.Desc.First.K4.RtPub

#print axioms OnBytes.Desc.First.K4.RtPub.hearPub_claims
