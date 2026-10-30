-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/GatesD1.lean: f₁ … f₆ of `configure_of_parts` at the written sizes and plans,
under the five facts on the run's shapes and the ledger's d₁ alone. One theorem.

Why. `gates_written` (Johnson/AtFull/Made/Gates.lean) takes one closed equation `hs` beside these.
It is a theorem (`lookup_scalars`, ScalarsKeyJoin.lean). `gates_written` keeps `hs` as a premise:
other files may call it.

What is said. `gates_written_d1 x first oneTime R d₁`: the same six, to the letter.

Limits. A joining. As Gates.lean's. Nothing on soundness.
-/
import Johnson.AtFull.Made.Gates
import Johnson.AtFull.Made.ScalarsKeyJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten.Joined (writtenSized)
open VerifiableInference.Number.ByRuns (proofThree keyThree)
open Johnson.G (pricedEntryFull)

theorem gates_written_d1 (x : Shapes) (first oneTime : Planned) (R : ShapesRead x first)
    (d₁ : Plan.oneTimePlan writtenSized.key = .ok oneTime) :
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
  gates_written x first oneTime R d₁ lookup_scalars

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.gates_written_d1
