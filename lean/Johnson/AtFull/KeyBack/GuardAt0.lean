-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/GuardAt0.lean: ONE CLOSED FACT: `Key.rangesNumbers`' last test
(Johnson/Desc/Key/Ranges.lean), at the key file's first written plan, the typed sizes and the place
18805: two stages or more, and the names from that place on are those that the stages ask. By an
evaluation in Lean's kernel (`decide +kernel`).
Limits. A closed fact on written files: it names no m and no public file. That a planner's answer
holds these written plans or sizes is not said here. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.KPlans
import Johnson.Desc.K12.Plan.TestCut
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Lk6.AtPlan (keyFull)

set_option maxRecDepth 1000000 in
/-- The test says yes. -/
theorem guard_A :
    (decide (2 ≤ keyFull.ranges.x.stages.length) &&
      ((roundsA.drop 18805).take (1 + H2U.towerLen keyFull.ranges.x.stages)).map (·.name) ==
        "BAT" :: H2U.towerNames keyFull.ranges.x.stages) = true := by decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.guard_A
