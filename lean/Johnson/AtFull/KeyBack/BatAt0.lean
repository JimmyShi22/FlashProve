-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/BatAt0.lean: ONE CLOSED FACT: the first round named "BAT" of the key file's
first written plan stands at 18805. By an evaluation in Lean's kernel (`decide +kernel`): a walk
over all the plan's rounds.
Limits. A closed fact on written files: it names no m and no public file. That a planner's answer
holds these written plans or sizes is not said here. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.KPlans
import Johnson.Desc.K12.Plan.TestCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params

set_option maxRecDepth 1000000 in
/-- Where the first "BAT" stands. -/
theorem bat_first_A : (H2U.batPlaces roundsA).head? = some 18805 := by decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.bat_first_A
