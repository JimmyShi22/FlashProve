-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/SeatedPlan.lean: THE SMALLNESS TEST: "FIXED BEFORE THE DRAW": ALL THE LAW'S
PREMISES AS ONE TEST WITH CODE. A DEFINITION. NO THEOREM HERE. NO SOUNDNESS IS CLAIMED.

  `beforeB F seat p i`: the file's test on the plan says yes, and the i-th block of the first
    chain's flat list has the kind's declared rounds, its field `before` and its test on the plan at
    p.
What a yes gives is Johnson/Desc/First/K8/LawSeatedPlan.lean's `before_of_test`. The block's
decision is not read: so the test can say yes at a block that a seat has laid with a guard behind
its decision.

-/
import Johnson.Desc.First.K8.Hear

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8

/-- **One test with code.** -/
def beforeB {Xi : Type} (F : FileDescription Xi) (seat : Seat F.S₁) (p : Par) (i : Nat) : Bool :=
  F.planOk &&
    match F.first.blocksInOrder[i]? with
    | none => false
    | some b =>
      b.rounds == (approximateRangeProofDrawKind (Cl := F.Cl) seat p).rounds &&
        b.before == (approximateRangeProofDrawKind (Cl := F.Cl) seat p).before &&
        b.planOk == (approximateRangeProofDrawKind (Cl := F.Cl) seat p).planOk

end VerifiableInference.Desc.First.K8
