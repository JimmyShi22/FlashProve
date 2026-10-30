-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Plans/PlansSameC.lean: THE PLANNER's THIRD WRITTEN LIST OF ROUNDS FOR THE PROOF FILE
(`proofThree.C`, Johnson/Desc/Ok/NumberPrices/ProofAtWritten.lean) HAS THE ENTRIES OF THE DRY RUNS'
THIRD WRITTEN LIST (`dryProofFull.2.2`, Johnson/G/DryProofLit.lean; 30 rounds), AND NONE OF THEM
BEARS `Fmt.recordName`. One small decision of Lean's kernel (`sameB`, PlansLaw.lean).
Limits. The full size alone. Both lists are WRITTEN values. Nothing on soundness. On hiding nothing.

-/
import Johnson.AtFull.Plans.PlansLaw
import Johnson.Desc.Ok.NumberPrices.ProofAtWritten
import Johnson.G.DryProofLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Plans
open VerifiableInference.Number.ByRuns (proofThree)
open Johnson.G (dryProofFull)

/-- **The Bool says yes.** -/
theorem same_C : sameB proofThree.C.plan.plan (dryProofFull.2.2.map (·.1.entry)) = true := by
  decide +kernel

end Johnson.AtFull.Plans

#print axioms Johnson.AtFull.Plans.same_C
