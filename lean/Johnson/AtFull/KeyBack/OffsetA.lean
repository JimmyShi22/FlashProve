-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/OffsetA.lean: HOW MANY OF THE FIRST CHAIN's WRITTEN PLAN's ENTRIES ARE NO
ROUNDS. One closed fact, by the kernel, alone in its file: it walks a list of 18,852 twice.

`offset_A`: the number of entries of `keyThree.A.plan.plan`
(Johnson/Desc/Ok/NumberPrices/KeyAtWritten.lean) less the number of its rounds is 1.
Limits. It names no m and no public file: that the written values are the planner's at any public
files is not said here. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.TreesKOfRounds
import Johnson.AtFull.KeyBack.SentKey
import Johnson.Desc.Ok.NumberPrices.KeyAtWritten
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G.OfPlan
open Johnson.G (keySends0 keySends1 keySends2)
open VerifiableInference.Number.ByRuns (keyThree)
open Lk6.AtPlan (keyFull)

set_option maxRecDepth 1000000 in
/-- How many of the first chain's plan's entries are no rounds. -/
theorem offset_A :
    keyThree.A.plan.plan.entries.length - keyThree.A.plan.plan.rounds.length = 1 := by
  decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.offset_A
