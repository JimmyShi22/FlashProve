-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ScalarsRun.lean: the run of the key file's lookups' routine on an empty plan
returns, at the written sizes. One theorem, alone in its file: it may run away.

Why. It is piece (A) of "the lookups' count returns 34,933" (`hs` of `gate_ranges_of`,
Johnson/AtFull/Made/GateRanges.lean): the premise of `lookupScalars_of_returns` (ScalarsLaw.lean).

What is said. `lookups_run_returns`: the run's answer is there: by an evaluation in Lean's kernel
(`decide +kernel`: no tactic of the library's own).

Limits. The written sizes alone. Nothing on soundness.
-/
import Johnson.Goal.Written.Made
import OnBytes.Params.Configure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten.Joined (writtenSized)

set_option maxHeartbeats 0 in
theorem lookups_run_returns :
    ((forEach (Plan.lookupSizes writtenSized.key.ranges.x writtenSized.key.ranges.matrix)
      planLookup) { set := writtenSized.key.set }).toOption.isSome = true := by decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.lookups_run_returns
