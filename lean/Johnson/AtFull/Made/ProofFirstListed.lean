-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ProofFirstListed.lean: the list of the rounds of the proof file's first chain,
at the written sizes and the written arms, is the first of the proof file's written priced plans,
field by field. One closed fact, by an evaluation in Lean's kernel (`decide +kernel`),
alone in its file. A law file; no running text imports it. The like for the key file:
Johnson/Goal/Numbers/KeyFirstListed.lean.

Definitions.
  `proofFirstListed`: the setting of `proofSizedFull` with the rounds of `Plan.firstChainList`
    (OnBytes/Plan/PlanListsReq.lean) at `proofSizedFull`, `subW` and `listW`.
Statements.
  `ride_proof_first`: the test `rideB` (Johnson/Desc/Ok/NumberPrices/ByRuns.lean: the setting, and
    all seven fields of every round, in one walk) says yes against `proofThree.A`.
  `proof_first_listed`: so proofFirstListed = proofThree.A.plan.

Limits. No routine of the planner is evaluated here. Both sides stand on prints of the library's own
planner at one set of public files. Nothing says that an error bounds a count. Nothing on soundness.

-/
import Johnson.AtFull.Made.ArmList
import Johnson.Desc.Ok.PlanWritten.SizedLit
import Johnson.Desc.Ok.NumberPrices.ProofAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Number.ByRuns (proofThree rideB ride_eq)

/-- The setting of the written sizes with the rounds of the first chain's list. -/
def proofFirstListed : Planned :=
  ⟨proofSizedFull.set,
    (Plan.firstChainList proofSizedFull subW (listW proofSizedFull.set) []).map
      (·.round proofSizedFull.set .request)⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem ride_proof_first : rideB 60000 proofFirstListed proofThree.A = true := by
  decide +kernel

/-- **The listed plan is the first written plan.** -/
theorem proof_first_listed : proofFirstListed = proofThree.A.plan := ride_eq ride_proof_first

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.ride_proof_first
#print axioms Johnson.AtFull.Made.proof_first_listed
