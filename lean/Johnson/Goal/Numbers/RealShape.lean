-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/RealShape.lean: two written values of the sizes of the linear test on the
committed table, for a proof file at the full size, are one. The first: what the planner's sizing
routine returns at typed arguments (`realSized`, Johnson/Desc/K1/Law/CondReal.lean). The second: the
field `batch` of the written sizes of a proof file (`proofSizedFull`,
Johnson/Desc/Ok/PlanWritten/SizedLit.lean). And the written sizes' shape of a request is the written
shape of Johnson/Desc/ReqLit/Full.lean. Closed facts.

What it is for. The laws on the sub-protocols K13 and K14 are stated at the value x that `realSized`
returns. The test that holds the planner's sizes against a written value at the run
(`sizedPinnedAt`, Johnson/Desc/Ok/PlanWritten/SizedTest.lean) gives `proofSizedFull`. These facts
carry the one to the other.

Statements.
  `real_shape`: where `realSized` returns (x, `codesFull2`): x.shape is
    `proofSizedFull.batch.shape`.
  `real_batch`: there x is `proofSizedFull.batch`, whole: by the comparison field by field `sameLin`
    and its law `sameLin_eq` (Johnson/Desc/Ok/PlanWritten/SizedTestLaws.lean).
  `request_written`: `proofSizedFull.request` is `ReqLit.shapeFull`.
By evaluations in Lean's kernel (`decide +kernel`): one in each.

Limits. Nothing says that a planner's run returns either value. Nothing on soundness.
-/
import Johnson.Desc.K1.Law.CondReal
import Johnson.Desc.Ok.PlanWritten.SizedTestLaws
import Johnson.Desc.ReqLit.Full

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Johnson.G
open VerifiableInference.PlanWritten (proofSizedFull sameLin sameLin_eq)
open VerifiableInference.Desc.K1 (realSized)

/-- **The typed shape is the written sizes' shape.** -/
theorem real_shape {x : LinSized} (hx : realSized = some (x, codesFull2)) :
    x.shape = proofSizedFull.batch.shape := by
  have h : (realSized.any fun p => decide (p.1.shape = proofSizedFull.batch.shape)) = true := by
    decide +kernel
  rw [hx, Option.any_some] at h
  exact of_decide_eq_true h

/-- **The typed sizes are the written sizes' field, whole.** -/
theorem real_batch {x : LinSized} (hx : realSized = some (x, codesFull2)) :
    x = proofSizedFull.batch := by
  have h : (realSized.any fun p => sameLin p.1 proofSizedFull.batch) = true := by decide +kernel
  rw [hx, Option.any_some] at h
  exact sameLin_eq h

/-- The written sizes' shape of a request is the written shape. -/
theorem request_written :
    proofSizedFull.request = VerifiableInference.Desc.ReqLit.shapeFull := by decide +kernel

end Desc.K14.Law

#print axioms Desc.K14.Law.real_shape
#print axioms Desc.K14.Law.real_batch
#print axioms Desc.K14.Law.request_written
