-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/PlansAtFull.lean: the six written plans of a key file and of a proof file of
full size pass the tests that the laws of Johnson/AtFull/Made/ReadsOfConfigure.lean ask of a plan.

The plans are `keyThree` and `proofThree` (Johnson/Desc/Ok/NumberPrices/KeyAtWritten.lean,
ProofAtWritten.lean). That each fits the format's words is proved (`key_fit0` to `proof_fit2`,
PlansAtWritten.lean). The rest are closed facts, by Lean's kernel (`decide +kernel`), on the
distinct rounds and the runs (Johnson/AtFull/Made/PlanTools.lean): no plan is unrolled.

`planB_key0` to `planB_proof2`: each plan fits, is in order, and has the format's names alone.
`sameWords_key`, `sameWords_proof`: a file's three plans have the same six settings.
`noSample_key1`, `noSample_key2`, `noSample_proof0` to `noSample_proof2`: no entry for a table's own
sample. The key file's first plan has such an entry, and nothing is asked of it there.
`planB_small`, `planB_rejects`: a small plan that passes, and negative tests that each change one
entry of it.

Limits. That the written plans are what the planner makes is not said here. Nothing on soundness.

-/
import Johnson.AtFull.Made.PlanTools
import Johnson.Desc.Ok.NumberPrices.PlansAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open VerifiableInference.Number.ByRuns (keyThree proofThree key_fit0 key_fit1 key_fit2 proof_fit0
  proof_fit1 proof_fit2)

set_option maxRecDepth 1000000 in
theorem planB_key0 : planB keyThree.A.plan.plan = true :=
  planB_of_lit keyThree.A key_fit0 (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 1000000 in
theorem planB_key1 : planB keyThree.B.plan.plan = true :=
  planB_of_lit keyThree.B key_fit1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 1000000 in
theorem planB_key2 : planB keyThree.C.plan.plan = true :=
  planB_of_lit keyThree.C key_fit2 (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 1000000 in
theorem planB_proof0 : planB proofThree.A.plan.plan = true :=
  planB_of_lit proofThree.A proof_fit0 (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 1000000 in
theorem planB_proof1 : planB proofThree.B.plan.plan = true :=
  planB_of_lit proofThree.B proof_fit1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 1000000 in
theorem planB_proof2 : planB proofThree.C.plan.plan = true :=
  planB_of_lit proofThree.C proof_fit2 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem sameWords_key : sameWords keyThree.A.plan.plan keyThree.B.plan.plan = true ∧
    sameWords keyThree.A.plan.plan keyThree.C.plan.plan = true :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem sameWords_proof : sameWords proofThree.A.plan.plan proofThree.B.plan.plan = true ∧
    sameWords proofThree.A.plan.plan proofThree.C.plan.plan = true :=
  ⟨by decide +kernel, by decide +kernel⟩

set_option maxRecDepth 1000000 in
theorem noSample_key1 : noSample keyThree.B.plan.plan = true :=
  noSample_of_lit keyThree.B (by decide +kernel)

set_option maxRecDepth 1000000 in
theorem noSample_key2 : noSample keyThree.C.plan.plan = true :=
  noSample_of_lit keyThree.C (by decide +kernel)

set_option maxRecDepth 1000000 in
theorem noSample_proof0 : noSample proofThree.A.plan.plan = true :=
  noSample_of_lit proofThree.A (by decide +kernel)

set_option maxRecDepth 1000000 in
theorem noSample_proof1 : noSample proofThree.B.plan.plan = true :=
  noSample_of_lit proofThree.B (by decide +kernel)

set_option maxRecDepth 1000000 in
theorem noSample_proof2 : noSample proofThree.C.plan.plan = true :=
  noSample_of_lit proofThree.C (by decide +kernel)

/-- A plan with the third written key plan's settings and two entries, of which the first is the
entry for a table's own sample. -/
def twoEntries (e : Fmt.Entry) : Fmt.Plan :=
  { keyThree.C.plan.plan with entries := [{ name := Fmt.recordName, count := 1 }, e] }

/-- With a second entry that is in order the small plan passes. So each negative test below fails
for what it changes in that entry. -/
theorem planB_small : planB (twoEntries { name := "SEAL", count := 1 }) = true := by decide +kernel

/-- Negative tests: a name that is none of the format's; a second entry for a table's own sample; a
first word other than 1; a word of 2 ^ 64. -/
theorem planB_rejects :
    (planB (twoEntries { name := "NO SUCH ROUND", count := 1 }),
      planB (twoEntries { name := Fmt.recordName, count := 1 }),
      planB (twoEntries { name := "SEAL", count := 2 }),
      planB (twoEntries { name := "SEAL", count := 1, work := 2 ^ 64 })) =
      (false, false, false, false) := by decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.planB_key0
#print axioms Johnson.AtFull.Made.planB_key1
#print axioms Johnson.AtFull.Made.planB_key2
#print axioms Johnson.AtFull.Made.planB_proof0
#print axioms Johnson.AtFull.Made.planB_proof1
#print axioms Johnson.AtFull.Made.planB_proof2
#print axioms Johnson.AtFull.Made.sameWords_key
#print axioms Johnson.AtFull.Made.sameWords_proof
#print axioms Johnson.AtFull.Made.noSample_key1
#print axioms Johnson.AtFull.Made.noSample_key2
#print axioms Johnson.AtFull.Made.noSample_proof0
#print axioms Johnson.AtFull.Made.noSample_proof1
#print axioms Johnson.AtFull.Made.noSample_proof2
#print axioms Johnson.AtFull.Made.planB_small
#print axioms Johnson.AtFull.Made.planB_rejects
