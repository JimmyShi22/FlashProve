-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/KeyFirstRun.lean: one closed fact by an evaluation in Lean's kernel, alone in
its file: the run of the planner's first routine for a key file returns at the typed sizes of a key
of full size. The plan's verdict is not asked here.

Cost, measured twice: 305 s and 346 s; 13 GiB of the process's own memory.
Limits. It says that the run returns, not what. No soundness is claimed.
-/
import Johnson.Goal.Numbers.KeyFirstListed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params Lk6.AtPlan

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem key_run_returns :
    (finish keyFull.set .once (Plan.oneTimeRounds keyFull)).toOption.isSome = true := by
  decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.key_run_returns
