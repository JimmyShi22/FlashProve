-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ListsProof.lean: the lists of positions of the proof file's first written plan.
One theorem, alone in its file (the plan has 48,293 rounds).

Why. `ShapesRead.lists` (Johnson/AtFull/Made/Gates.lean) asks `listsOf first = listsFull` of the
plan that `firstPlan` returns (the ledger's e₁). Where that plan is the first written plan
(`proofThree.A.plan`, Johnson/Desc/Ok/NumberPrices/ProofAtWritten.lean), the fact is closed.

What is said. `lists_proof`: `listsOf proofThree.A.plan = listsFull`: by an evaluation in Lean's
kernel. `lists_of_written`: so `ShapesRead.lists` at every plan that is the first written plan.

Limits. That `firstPlan` returns the first written plan is said nowhere here. Nothing on soundness.

-/
import Johnson.AtFull.Made.GateLinks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten.Joined (writtenSized)
open VerifiableInference.Number.ByRuns (proofThree keyThree)
open Johnson.G (pricedEntryFull)

set_option maxRecDepth 1000000 in
theorem lists_proof : listsOf proofThree.A.plan = listsFull := by decide +kernel

theorem lists_of_written {first : Planned} (h : first = proofThree.A.plan) :
    listsOf first = listsFull := by
  rw [h]
  exact lists_proof

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.lists_proof
#print axioms Johnson.AtFull.Made.lists_of_written
