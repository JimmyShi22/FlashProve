-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/GateTable.lean: the planner's third gate says no at the written sizes and the
written plans. One definition, two theorems, one plant.

Why. `Params.configure` (OnBytes/Params/Configure.lean) refuses where `missedOnTheTable`
(OnBytes/Params/Gate.lean) says yes. It is the premise f₃ of `configure_of_parts`
(Johnson/AtFull/Made/Ledger.lean). OF THE RUN's SHAPES x IT READS ONE NUMBER: `x.sub.pendingRows`.

What is said. `gateTableAt n`: the gate's call in `configure`, to the letter, at `recordLines`,
`writtenSized`, the proof file's second and third written plans, the key file's second and third,
the entry file's, with n for the pending rows. `gate_table`: at n = 13 it says false: by an
evaluation in Lean's kernel. `gate_table_of`: so at every x with 13 pending rows.
`gate_table_plant`: at 100,000 pending rows it says true (no room among the index masks): the test
can fail.

Limits. The written values alone. That a run's shapes have 13 pending rows is a premise
(`shapes.sub.pendingRows = X.NGr + 1`: Johnson/Desc/First/Link/Law/RowsOfMade.lean). Nothing on
soundness.
-/
import Johnson.Goal.Written.Made
import OnBytes.Params.Configure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten.Joined (writtenSized)
open VerifiableInference.Number.ByRuns (proofThree keyThree)
open Johnson.G (pricedEntryFull)

/-- The third gate's call in `configure` at the written values, with n pending rows. -/
def gateTableAt (n : Nat) : Bool :=
  missedOnTheTable recordLines
    ⟨writtenSized.proof.batch, writtenSized.proof.codes, proofThree.B.plan, proofThree.C.plan, n, 0⟩
    ⟨writtenSized.key.once, writtenSized.key.codes, keyThree.B.plan, keyThree.C.plan,
      if sumT (writtenSized.key.ranges.x.lookups.map (·.parts.length)) != 0 then
        sumT (writtenSized.key.ranges.x.lookups.map (·.parts.length)) else 1,
      sumT (writtenSized.key.ranges.x.lookups.map (·.parts.length))⟩
    writtenSized.link writtenSized.entryCodes pricedEntryFull

/-- **f₃ at the written values and 13 pending rows.** -/
theorem gate_table : gateTableAt 13 = false := by decide +kernel

/-- In the ledger's own letters, at shapes with 13 pending rows. -/
theorem gate_table_of (x : Shapes) (hx : x.sub.pendingRows = 13) :
    missedOnTheTable recordLines
      ⟨writtenSized.proof.batch, writtenSized.proof.codes, proofThree.B.plan, proofThree.C.plan,
        x.sub.pendingRows, 0⟩
      ⟨writtenSized.key.once, writtenSized.key.codes, keyThree.B.plan, keyThree.C.plan,
        if sumT (writtenSized.key.ranges.x.lookups.map (·.parts.length)) != 0 then
          sumT (writtenSized.key.ranges.x.lookups.map (·.parts.length)) else 1,
        sumT (writtenSized.key.ranges.x.lookups.map (·.parts.length))⟩
      writtenSized.link writtenSized.entryCodes pricedEntryFull = false := by
  rw [hx]
  exact gate_table

theorem gate_table_plant : gateTableAt 100000 = true := by decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.gate_table
#print axioms Johnson.AtFull.Made.gate_table_of
#print axioms Johnson.AtFull.Made.gate_table_plant
