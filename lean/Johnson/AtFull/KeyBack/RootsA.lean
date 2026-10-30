-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/RootsA.lean: AT EVERY ROUND OF THE FIRST CHAIN AS MANY TREES AS THE ENTRY
HAS ROOTS. One closed fact, by the kernel, alone in its file: 18,851 rounds, at each a count over
six numbers.

`roots_A`: the test `rootsC` (Johnson/Unfolds/TreesAt.lean) accepts the rounds
of `keyThree.A.plan.plan` with [0, 2, 18811, 18818, 18824, 18848].
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
/-- At every round of the first chain: as many trees as the entry has roots. -/
theorem roots_A :
    Johnson.Unfolds.rootsC keyThree.A.plan.plan.rounds
      [0, 2, 18811, 18818, 18824, 18848] = true := by
  decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.roots_A
