-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ScalarsKeyJoin.lean: THE LOOKUPS' COUNT OF SCALARS AT THE WRITTEN SIZES OF A KEY
FILE RETURNS 34,933: the three pieces joined; and so the planner's second gate under the ledger's d₁
alone. Two theorems.

Why. `gate_ranges_of` (Johnson/AtFull/Made/GateRanges.lean) takes two premises: the ledger's d₁ and
"`Plan.lookupScalars writtenSized.key = .ok 34933`". Asked whole, Lean's kernel does not answer the
second (three trials: an abort after 701 s; out of memory at 64 GiB after 1314 s; "deep recursion
detected" after 632 s). In three pieces it does.

What is said. `lookup_scalars`: the equation: (A) the run on the empty plan returns
(`lookups_run_returns`, ScalarsRun.lean: the kernel, 316 s); (B) where it returns, the count is the
plain list's (`lookupScalars_of_returns`, ScalarsLaw.lean: by the library's `runs_lookup` and
`runs_forEach`); (C) over the plain list the count is 34,933 (`scalars_on_key`, ScalarsOnKey.lean:
the kernel). `gate_ranges_d1`: so f₂ of `configure_of_parts`, to the letter, under its d₁ alone.

Limits. The written sizes alone. Nothing on soundness.
-/
import Johnson.AtFull.Made.ScalarsRun
import Johnson.AtFull.Made.ScalarsOnKey
import Johnson.AtFull.Made.GateRanges

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten.Joined (writtenSized)

/-- **The lookups' count returns 34,933.** -/
theorem lookup_scalars : Plan.lookupScalars writtenSized.key = .ok 34933 := by
  rw [lookupScalars_of_returns writtenSized.key lookups_run_returns, scalars_on_key]

/-- **f₂, in the ledger's own letters, under its d₁ alone.** -/
theorem gate_ranges_d1 {oneTime : Planned}
    (d₁ : Plan.oneTimePlan writtenSized.key = .ok oneTime) :
    Plan.missedInTheRanges writtenSized.key = false :=
  gate_ranges_of d₁ lookup_scalars

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.lookup_scalars
#print axioms Johnson.AtFull.Made.gate_ranges_d1
