-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/CutAtU.lean: FIVE CLOSED FACTS ON THE KEY FILE's SECOND WRITTEN PLAN (68
entries) AND THE TYPED SIZES. Each by an evaluation in Lean's kernel (`decide +kernel`).
  `bats_B`: its rounds named "BAT" stand at 8 and 43, and nowhere else.
  `cutU_B`, `cutO_B`: `H2U.cutOn` (Johnson/Desc/K12/Plan/PlaceOfPlan.lean) returns at 8 with the
    stages of the test on the folded row's group, and at 43 with those of the test on Omega's group.
  `rootsU_B`, `rootsO_B`: the entries in front receive 3 and 7 roots.
Limits. A closed fact on written files: it names no m and no public file. That a planner's answer
holds these written plans or sizes is not said here. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.KPlans
import Johnson.Desc.K12.Plan.PlaceOfPlan
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Lk6.AtPlan (keyFull)

theorem bats_B : H2U.batPlaces entriesB = [8, 43] := by decide +kernel

theorem cutU_B : (H2U.cutOn entriesB 1 8 keyFull.once.shape.testU).isSome = true := by
  decide +kernel

theorem cutO_B : (H2U.cutOn entriesB 1 43 keyFull.once.shape.testOmega).isSome = true := by
  decide +kernel

theorem rootsU_B : ((entriesB.take 8).map (·.roots)).foldl (· + ·) 0 = 3 := by decide +kernel

theorem rootsO_B : ((entriesB.take 43).map (·.roots)).foldl (· + ·) 0 = 7 := by decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.bats_B
#print axioms Johnson.AtFull.KeyBack.cutU_B
#print axioms Johnson.AtFull.KeyBack.cutO_B
#print axioms Johnson.AtFull.KeyBack.rootsU_B
#print axioms Johnson.AtFull.KeyBack.rootsO_B
