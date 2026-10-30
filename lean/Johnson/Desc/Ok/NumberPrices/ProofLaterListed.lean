-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/NumberPrices/ProofLaterListed.lean: two routines of the planner, at the written
sizes of a proof file of full size (`proofSizedFull`, Johnson/Desc/Ok/PlanWritten/SizedLit.lean),
return the second and the third of the proof file's written priced plans
(Johnson/Desc/Ok/NumberPrices/ProofAtWritten.lean), field by field: 68 and 30 rounds. And these
written sizes are such as the library's laws on a price that covers a proved count ask
(Johnson/Prices/): so these laws' premise, a plan that the planner returns at such sizes, is paid at
the written plans, by closed facts.

Lean's kernel evaluates each call whole and holds the answer against the written plan: the setting,
and all seven fields of every round (`rideAt`, Johnson/Desc/Ok/NumberPrices/ByRuns.lean). The
equations have no premise, and they name no public file, no digest and no hash.

Statements.
  `ride_proof_shared`, `ride_proof_second`: the two tests say yes. `proof_shared_written`,
    `proof_second_written`: so the two routines return the two written plans.
  `proof_sized_set`: the written sizes' setting is `recordSet`. `shared_at_record`,
    `second_at_record`: the two equations with `recordSet` for it.
  `batch_atRecord`, `batch_atRecordOwn`, `batch_numbers`: the written sizes of the test on the table
    are such as `AtRecord` (Johnson/Prices/Dear.lean) and `AtRecordOwn`
    (Johnson/Prices/SecondRecord.lean) ask, with 7 low variables, 64 requests and 22 row variables
    (the premises of `k14_shared_at_record`, Johnson/Prices/Record.lean).
  `shared_passes`, `second_passes`: the two written plans pass the library's test on a finished plan
    (`Passes`, Johnson/Prices/SharedExists.lean) at 28 and at 20 bits of work.
  `shared_tail_written`: the second written plan's rounds from place 7 on are those of the library's
    typed list `sharedTail`, then "SEAL"; at place 3 stands the typed "LOC". `second_list_written`:
    the third written plan's rounds are those of the typed list `secondList`. From
    `shared_rounds_at` and `second_rounds_at`.
  `ride_proof_shared_bent`: against the second written plan with one error doubled (`bentProof`,
    ProofAtWrittenTeeth.lean) the test says no.
By evaluations in Lean's kernel (`decide +kernel`): the three rides, `proof_sized_set`, the fields
of `batch_atRecord`, `batch_atRecordOwn`, `batch_numbers`, and inside `shared_passes`,
`second_passes`.

What of OnBytes/Model/ is used: nothing by name.

Limits. The written plans stand on prints of the library's own planner (see the head of
ProofAtWritten.lean), and the written sizes on one print. That the planner's sizes at any public
files are these is shown nowhere. Nothing on the proof file's first plan. What the laws of
Johnson/Prices/ then say of the written plans is not stated here. Nothing on soundness.

-/
import Johnson.Desc.Ok.NumberPrices.ProofAtWrittenTeeth
import Johnson.Desc.Ok.PlanWritten.SizedLit
import Johnson.Prices.SecondRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Number.ByRuns
open VerifiableInference VerifiableInference.PlanWritten
open OnBytes OnBytes.Params OnBytes.Params.Prices

/-! ## Two routines of the planner return two written plans -/

set_option maxRecDepth 1000000 in
theorem ride_proof_shared :
    rideAt 200 (sharedPlan proofSizedFull.set proofSizedFull.codes proofSizedFull.batch)
      proofThree.B = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem ride_proof_second :
    rideAt 200 (secondPlan proofSizedFull.set proofSizedFull.batch) proofThree.C = true := by
  decide +kernel

/-- **The planner's second routine, at the proof file's written sizes, returns the proof file's
second written plan.** -/
theorem proof_shared_written :
    sharedPlan proofSizedFull.set proofSizedFull.codes proofSizedFull.batch =
      .ok proofThree.B.plan :=
  rideAt_eq ride_proof_shared

/-- **Its third routine returns the third.** -/
theorem proof_second_written :
    secondPlan proofSizedFull.set proofSizedFull.batch = .ok proofThree.C.plan :=
  rideAt_eq ride_proof_second

/-! ## The written sizes are such as the laws on covered prices ask -/

/-- The written sizes' setting is the setting of the written lines. -/
theorem proof_sized_set : proofSizedFull.set = recordSet := by decide +kernel

theorem shared_at_record :
    sharedPlan recordSet proofSizedFull.codes proofSizedFull.batch = .ok proofThree.B.plan := by
  rw [← proof_sized_set]
  exact proof_shared_written

theorem second_at_record : secondPlan recordSet proofSizedFull.batch = .ok proofThree.C.plan := by
  rw [← proof_sized_set]
  exact proof_second_written

theorem batch_atRecord : AtRecord proofSizedFull.batch :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

theorem batch_atRecordOwn : AtRecordOwn proofSizedFull.batch :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- 7 low variables, 64 requests, 22 row variables. -/
theorem batch_numbers : proofSizedFull.batch.shape.kLo = 7 ∧
    proofSizedFull.batch.lines.requests = 64 ∧ proofSizedFull.batch.shape.kRow = 22 := by
  decide +kernel

/-- The second written plan passes the library's test on a finished plan, at 28 bits of work. -/
theorem shared_passes : Passes 28 proofThree.B.plan := passes_sound (by decide +kernel)

/-- The third passes it at 20 bits. -/
theorem second_passes : Passes 20 proofThree.C.plan := passes_sound (by decide +kernel)

/-! ## The written plans' rounds are the library's typed lists -/

/-- **From place 7 on the second written plan's rounds are the typed list's, then "SEAL"; at place
3 stands the typed "LOC".** -/
theorem shared_tail_written :
    proofThree.B.plan.rounds.drop 7 = (sharedTail ++ [sealRound]).map (·.round recordSet .shared) ∧
      proofThree.B.plan.rounds[3]? = some (sharedLoc.round recordSet .shared) :=
  shared_rounds_at batch_atRecord shared_at_record

/-- **The third written plan's rounds are the typed list's.** -/
theorem second_list_written :
    proofThree.C.plan.rounds = secondList.map (·.round recordSet .request) :=
  second_rounds_at batch_atRecordOwn second_at_record

/-! ## Where the test bites -/

set_option maxRecDepth 1000000 in
/-- Against the second written plan with one error doubled the test says no. -/
theorem ride_proof_shared_bent :
    rideAt 200 (sharedPlan proofSizedFull.set proofSizedFull.codes proofSizedFull.batch)
      bentProof.B = false := by
  decide +kernel

end VerifiableInference.Number.ByRuns

#print axioms VerifiableInference.Number.ByRuns.ride_proof_shared
#print axioms VerifiableInference.Number.ByRuns.ride_proof_second
#print axioms VerifiableInference.Number.ByRuns.proof_shared_written
#print axioms VerifiableInference.Number.ByRuns.proof_second_written
#print axioms VerifiableInference.Number.ByRuns.proof_sized_set
#print axioms VerifiableInference.Number.ByRuns.shared_at_record
#print axioms VerifiableInference.Number.ByRuns.second_at_record
#print axioms VerifiableInference.Number.ByRuns.batch_atRecord
#print axioms VerifiableInference.Number.ByRuns.batch_atRecordOwn
#print axioms VerifiableInference.Number.ByRuns.batch_numbers
#print axioms VerifiableInference.Number.ByRuns.shared_passes
#print axioms VerifiableInference.Number.ByRuns.second_passes
#print axioms VerifiableInference.Number.ByRuns.shared_tail_written
#print axioms VerifiableInference.Number.ByRuns.second_list_written
#print axioms VerifiableInference.Number.ByRuns.ride_proof_shared_bent
