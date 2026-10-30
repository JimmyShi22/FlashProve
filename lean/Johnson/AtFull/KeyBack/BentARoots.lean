-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/BentARoots.lean: A NEGATIVE TEST: THE COUNT OF TREES AGAINST THE ROOTS AT
THE FIRST CHAIN, AT A BENT LIST. By the kernel, alone in its file: 18,851 rounds.

`roots_A_bent`: with the last round bent by one, `rootsC` does not accept. It adds no truth beside
`roots_A`.
Limits. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.TreesKOfRounds
import Johnson.AtFull.KeyBack.SentKey
import Johnson.Unfolds.MergeSort
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
theorem roots_A_bent : ¬ (Johnson.Unfolds.rootsC keyThree.A.plan.plan.rounds
    [0, 2, 18811, 18818, 18824, 18849] = true) := by
  decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.roots_A_bent
