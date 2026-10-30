-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/CutAtW.lean: TWO CLOSED FACTS ON THE KEY FILE's THIRD WRITTEN PLAN (30
entries) AND THE TYPED SIZES. Each by an evaluation in Lean's kernel (`decide +kernel`).
  `bat_first_C`: its first round named "BAT" stands at 0.
  `cutW_C`: `H2U.cutOn` (Johnson/Desc/K12/Plan/PlaceOfPlan.lean) returns there with the stages of
    the own test.
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

theorem bat_first_C : (H2U.batPlaces entriesC).head? = some 0 := by decide +kernel

theorem cutW_C : (H2U.cutOn entriesC 2 0 keyFull.once.shape.testOwn).isSome = true := by
  decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.bat_first_C
#print axioms Johnson.AtFull.KeyBack.cutW_C
