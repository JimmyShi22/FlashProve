-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/OnPlan/OkPlan.lean: the tests on a planner's answer p alone that the description's
decision is meant to ask itself, at its head. A definition with code; no theorem.

IT STANDS OVER NO FILE THAT IMPORTS Mathlib.

Main name:
  OkD.plan p: OkD.desc p (Johnson/Desc/OnPlan/OkDesc.lean), OkD.sched p (OkSched.lean),
    OkD.read p (OkRead.lean) and OkD.lists p (OkLists.lean): the plan alone; no size; no
    planner; no hash function.

What is not claimed. THAT IT SAYS YES AT ANY p: nothing is evaluated here. Nothing on soundness, on
an honest prover or on hiding.

-/
import Johnson.Desc.OnPlan.OkSched
import Johnson.Desc.OnPlan.OkRead
import Johnson.Desc.OnPlan.OkLists

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.OkD
open OnBytes

/-- **The tests on the plan alone.** -/
def plan (p : Model.Verify.Planned) : Bool := desc p && sched p && read p && lists p

end VerifiableInference.OnPublicFiles.OkD
