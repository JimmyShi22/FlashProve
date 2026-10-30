-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/BentA.lean: NEGATIVE TESTS: THREE TESTS OF `ChainFits` AT THE FIRST CHAIN,
AT A BENT VALUE. By the kernel.

Each theorem is a «not»: at a bent offset, list of rounds or bound the kernel brings the very term
of OffsetA.lean, RoundsA.lean, BelowA.lean to «false». The fourth, on the count, stands alone in
BentARoots.lean. They add no truth beside the positives.
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
theorem offset_A_bent :
    ¬ (keyThree.A.plan.plan.entries.length - keyThree.A.plan.plan.rounds.length = 0) := by
  decide +kernel

theorem rounds_A_bent : roundsOfChain keySends0 1 [] ≠ [0, 2, 18811, 18818, 18824, 18849] := by
  unfold roundsOfChain
  simp only [Johnson.Unfolds.mergeSort_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem below_A_bent : ¬ ((([0, 2, 18811, 18818, 18824, 18851] : List Nat).all fun r =>
    decide (r < keyThree.A.plan.plan.rounds.length)) = true) := by
  decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.offset_A_bent
#print axioms Johnson.AtFull.KeyBack.rounds_A_bent
#print axioms Johnson.AtFull.KeyBack.below_A_bent
