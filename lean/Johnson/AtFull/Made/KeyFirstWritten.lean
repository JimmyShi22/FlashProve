-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/KeyFirstWritten.lean: the planner's first routine for a key file, at the typed
sizes of a key of full size, RETURNS THE FIRST WRITTEN PLAN: two closed equations. Calls alone: the
join
(KeyFirst.lean) at the four closed facts (KeyFirstRun.lean, KeyFirstVerdict.lean).

  `key_finish_written`: the run alone. `key_first_written`: with the plan's verdict.

It pays what Johnson/Goal/Numbers/KeyFirstListed.lean's Limits leave open ("That
`Plan.oneTimePlan keyFull` returns is not shown").
Limits. That the sizes of a key at any public files are `keyFull` is not said here. No soundness is
claimed.
-/
import Johnson.AtFull.Made.KeyFirst
import Johnson.AtFull.Made.KeyFirstRun
import Johnson.AtFull.Made.KeyFirstVerdict

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open VerifiableInference.Number.ByRuns OnBytes OnBytes.Params Lk6.AtPlan Johnson.G

theorem key_finish_written :
    finish keyFull.set .once (Plan.oneTimeRounds keyFull) = .ok keyThree.A.plan :=
  finish_of_run key_run_returns

/-- **`Plan.oneTimePlan keyFull` returns the first written plan.** -/
theorem key_first_written : Plan.oneTimePlan keyFull = .ok keyThree.A.plan :=
  oneTime_of_four key_run_returns key_rounds_hold key_words_fit key_one_distance

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.key_finish_written
#print axioms Johnson.AtFull.Made.key_first_written
