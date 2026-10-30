-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/GateKey.lean: the planner's test on a key file's values together says yes at the
written sizes. One theorem.

Why. `Params.configure` (OnBytes/Params/Configure.lean) refuses unless `Plan.keyOk z.key` says yes.
It is the premise f₅ of `configure_of_parts` (Johnson/AtFull/Made/Ledger.lean).

What is said. `gate_key`: at `writtenSized.key`: IT IS `keyOk_full`
(Johnson/Goal/PlanValues/KeyOkFull.lean), called: `writtenSized.key` is `keyFull` by unfolding. No
twin is typed.

Limits. The written sizes alone. Nothing on soundness.
-/
import Johnson.Goal.Written.Made
import Johnson.Goal.PlanValues.KeyOkFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten.Joined (writtenSized)

/-- **f₅ at the written sizes.** -/
theorem gate_key : Plan.keyOk writtenSized.key = true := Lk6.AtPlan.keyOk_full

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.gate_key
