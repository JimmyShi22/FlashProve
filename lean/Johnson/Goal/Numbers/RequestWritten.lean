-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/RequestWritten.lean: two written values of the shape of a request at the full
size are one: the field `request` of the written sizes of a proof file (`proofSizedFull`,
Johnson/Desc/Ok/PlanWritten/SizedLit.lean) and `ReqLit.shapeFull` (Johnson/Desc/ReqLit/Full.lean). A
closed fact, in a file that imports these two alone.

Statement. `request_shape_written`. By an evaluation in Lean's kernel (`decide +kernel`). The same
sentence stands as `Desc.K14.Law.request_written` in Johnson/Goal/Numbers/RealShape.lean, above a
larger cone.

Limits. Nothing says that a planner returns either value. Nothing on soundness.
-/
import Johnson.Desc.Ok.PlanWritten.SizedLit
import Johnson.Desc.ReqLit.Full

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten

/-- The written sizes' shape of a request is the written shape. -/
theorem request_shape_written :
    proofSizedFull.request = VerifiableInference.Desc.ReqLit.shapeFull := by decide +kernel

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.request_shape_written
