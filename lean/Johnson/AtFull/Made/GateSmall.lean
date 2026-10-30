-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/GateSmall.lean: the planner's four small conditions hold at the written sizes of
a proof file. Four theorems, one plant.

Why. `Params.configure` (OnBytes/Params/Configure.lean) refuses unless: one identifier for
each segment; one notice at the start; a pending row; one plain scalar in the last segment alone. As
one Bool it is the premise f₆ of `configure_of_parts` (Johnson/AtFull/Made/Ledger.lean). OF THE
RUN's SHAPES x IT READS TWO NUMBERS: `x.identifiers.length` and `x.sub.pendingRows`.

What is said. `small_links`, `small_start`, `small_plain`: at `writtenSized.proof.request`: 25
segments; one notice at the start; the plain scalars are 24 times 0, then 1: each by an evaluation
in Lean's kernel. `gate_small_of`: so f₆, to the letter, at every x with 25 identifiers and a
pending row.

Limits. The written sizes alone. The two facts on x are premises. It can fail: at 24 identifiers the
first clause says yes (`gate_small_plant`). Nothing on soundness.
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

theorem small_links : writtenSized.proof.request.link.length = 25 := by decide +kernel

theorem small_start : writtenSized.proof.request.atStart.length = 1 := by decide +kernel

theorem small_plain : writtenSized.proof.request.link.map (·.plain) =
    List.replicate (25 - 1) 0 ++ [1] := by decide +kernel

/-- **f₆ at the written sizes.** -/
theorem gate_small_of (x : Shapes) (hi : x.identifiers.length = 25)
    (hp : x.sub.pendingRows ≠ 0) :
    (x.identifiers.length != writtenSized.proof.request.link.length ||
      writtenSized.proof.request.atStart.length != 1 || x.sub.pendingRows == 0 ||
      writtenSized.proof.request.link.map (·.plain) !=
        List.replicate (writtenSized.proof.request.link.length - 1) 0 ++ [1]) = false := by
  rw [small_links, small_start, small_plain, hi]
  simp [hp]

theorem gate_small_plant (x : Shapes) (hi : x.identifiers.length = 24) :
    (x.identifiers.length != writtenSized.proof.request.link.length ||
      writtenSized.proof.request.atStart.length != 1 || x.sub.pendingRows == 0 ||
      writtenSized.proof.request.link.map (·.plain) !=
        List.replicate (writtenSized.proof.request.link.length - 1) 0 ++ [1]) = true := by
  rw [small_links, hi]
  simp

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.small_links
#print axioms Johnson.AtFull.Made.small_start
#print axioms Johnson.AtFull.Made.small_plain
#print axioms Johnson.AtFull.Made.gate_small_of
#print axioms Johnson.AtFull.Made.gate_small_plant
