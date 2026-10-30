-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/GatesClosed.lean: f₁ … f₆ of `configure_of_parts` at the written sizes and
plans, UNDER THE FIVE FACTS ON THE RUN's SHAPES ALONE. Two theorems.

Why. `gates_written_d1` (Johnson/AtFull/Made/GatesD1.lean) takes the ledger's d₁ beside these. It is
a closed theorem (`key_first_written`, Johnson/AtFull/Made/KeyFirstWritten.lean).

What is said. `gate_ranges_closed`: f₂ at the written sizes: NO PREMISE. `gates_written_closed x
first R`: the six, to the ledger's letter, under `ShapesRead x first` alone.

Limits. A joining. As Gates.lean's. Nothing on soundness.
-/
import Johnson.AtFull.Made.GatesD1
import Johnson.AtFull.Made.KeyFirstWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten.Joined (writtenSized)
open VerifiableInference.Number.ByRuns (proofThree keyThree)
open Johnson.G (pricedEntryFull)

/-- **f₂ at the written sizes: closed.** -/
theorem gate_ranges_closed : Plan.missedInTheRanges writtenSized.key = false :=
  gate_ranges_d1 key_first_written

theorem gates_written_closed (x : Shapes) (first : Planned) (R : ShapesRead x first) :
    missedInTheLinks recordLines writtenSized.proof x.sub first = .ok false ∧
    Plan.missedInTheRanges writtenSized.key = false ∧
    missedOnTheTable recordLines
      ⟨writtenSized.proof.batch, writtenSized.proof.codes, proofThree.B.plan, proofThree.C.plan,
        x.sub.pendingRows, 0⟩
      ⟨writtenSized.key.once, writtenSized.key.codes, keyThree.B.plan, keyThree.C.plan,
        if sumT (writtenSized.key.ranges.x.lookups.map (·.parts.length)) != 0 then
          sumT (writtenSized.key.ranges.x.lookups.map (·.parts.length)) else 1,
        sumT (writtenSized.key.ranges.x.lookups.map (·.parts.length))⟩
      writtenSized.link writtenSized.entryCodes pricedEntryFull = false ∧
    missedInTheChecks recordLines x.rangeChecks writtenSized.key.once.shape.fold.columns
      writtenSized.link.shape.columnsFirst writtenSized.proof.batch.batches = false ∧
    Plan.keyOk writtenSized.key = true ∧
    (x.identifiers.length != writtenSized.proof.request.link.length ||
      writtenSized.proof.request.atStart.length != 1 || x.sub.pendingRows == 0 ||
      writtenSized.proof.request.link.map (·.plain) !=
        List.replicate (writtenSized.proof.request.link.length - 1) 0 ++ [1]) = false :=
  gates_written_d1 x first keyThree.A.plan R key_first_written

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.gate_ranges_closed
#print axioms Johnson.AtFull.Made.gates_written_closed
