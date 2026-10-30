-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/KeyFirstVerdict.lean: at the key file's first WRITTEN plan the three parts of
the plan's verdict (`Planned.holds`, OnBytes/Params/Planner.lean) say yes. Closed facts
by evaluations in Lean's kernel.

Limits. Both sides are written values. No soundness is claimed.
-/
import Johnson.Goal.Numbers.KeyFirstListed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open VerifiableInference.Number.ByRuns OnBytes OnBytes.Params Johnson.G

set_option maxRecDepth 1000000 in
theorem key_rounds_hold : keyThree.A.plan.roundsHold = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem key_words_fit : keyThree.A.plan.wordsFit = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem key_one_distance : keyThree.A.plan.oneDistance = true := by decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.key_rounds_hold
#print axioms Johnson.AtFull.Made.key_words_fit
#print axioms Johnson.AtFull.Made.key_one_distance
