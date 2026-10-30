-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Plans/PlansSameCNo.lean: A NEGATIVE TEST TO `same_C` (PlansSameC.lean): against the
dry runs'
third written list WITH ITS LAST ENTRY STRUCK the Bool says no. One small decision of Lean's kernel,
stated positively.
Limits. One fault at one place. The full size alone. Nothing on soundness. On hiding nothing.

-/
import Johnson.AtFull.Plans.PlansLaw
import Johnson.Desc.Ok.NumberPrices.ProofAtWritten
import Johnson.G.DryProofLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Plans
open VerifiableInference.Number.ByRuns (proofThree)
open Johnson.G (dryProofFull)

/-- **With the last entry struck the Bool says no.** -/
theorem same_C_refuses :
    sameB proofThree.C.plan.plan (dryProofFull.2.2.map (·.1.entry)).dropLast = false := by
  decide +kernel

end Johnson.AtFull.Plans

#print axioms Johnson.AtFull.Plans.same_C_refuses
