-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Plans/PlansSameB.lean: THE PLANNER's SECOND WRITTEN LIST OF ROUNDS FOR THE PROOF FILE
(`proofThree.B`, Johnson/Desc/Ok/NumberPrices/ProofAtWritten.lean) HAS THE ENTRIES OF THE DRY RUNS'
SECOND WRITTEN LIST (`dryProofFull.2.1`, Johnson/G/DryProofLit.lean; 68 rounds), AND NONE OF THEM
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
theorem same_B : sameB proofThree.B.plan.plan (dryProofFull.2.1.map (·.1.entry)) = true := by
  decide +kernel

end Johnson.AtFull.Plans

#print axioms Johnson.AtFull.Plans.same_B
