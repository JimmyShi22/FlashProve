-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/BelowA.lean: THE FIRST CHAIN's TREES' ROUNDS LIE BELOW THE NUMBER OF
ROUNDS. One closed fact, by the kernel, alone in its file.

`below_A`: each of [0, 2, 18811, 18818, 18824, 18848] lies below the number of rounds of
`keyThree.A.plan.plan`.
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
/-- Every tree's round lies below the number of rounds. -/
theorem below_A : (([0, 2, 18811, 18818, 18824, 18848] : List Nat).all fun r =>
    decide (r < keyThree.A.plan.plan.rounds.length)) = true := by
  decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.below_A
