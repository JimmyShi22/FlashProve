-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Later/SecondNo.lean: a negative test beside the fact that each of the last chain's
four sub-protocols passes its own test on the plan at the written values (`second_plan_rows`,
Johnson/AtFull/Desc/SecondShare.lean; the field b₃ of `LaterPaid`, Johnson/AtFull/Later/Paid.lean).

  `second_plan_bent`: the same test, by the library's own routines, at the written values but for
    one: the parameters of the last proximity test have one stage fewer. It rejects. By evaluation
    in Lean's kernel.

Nothing imports this file.

Limits. One bend, at one of the test's inputs: at which of the four sub-protocols and at which
clause the test rejects is not shown. Nothing on soundness or on hiding.

-/
import Johnson.AtFull.Desc.SecondShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Later
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.PlanWritten
open Johnson.AtFull.Desc

/-- **The test on the last chain's four sub-protocols can fail**: with one stage fewer in the
parameters of the last proximity test. -/
theorem second_plan_bent :
    (((secondAt (Third.p₁₄Z proofSizedFull.set proofSizedFull.codes proofSizedFull.batch)
      { piW with nums := { piW.nums with stages := piW.nums.stages.dropLast } }).retype
        (Cl' := ProofFile.Cl)).blocksInOrder).all (·.planOk) = false := by
  decide +kernel

end Johnson.AtFull.Later

#print axioms Johnson.AtFull.Later.second_plan_bent
