-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/BentC.lean: NEGATIVE TESTS: EACH TEST OF `ChainFits` AT THE SECOND CHAIN,
AT A BENT VALUE. By the kernel.

Each theorem is a «not»: at an offset, a list of rounds or a count that is bent by one, and at a
round set at the number of rounds, the first that is not below it, the kernel brings the very term
of FitsC.lean to «false». They add no truth beside the positives: they show that the decision can
come out the other way.
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
theorem offset_C_bent :
    ¬ (keyThree.C.plan.plan.entries.length - keyThree.C.plan.plan.rounds.length = 1) := by
  decide +kernel

theorem rounds_C_bent : roundsOfChain keySends2 0 [] ≠ [7, 14, 20, 27] := by
  unfold roundsOfChain
  simp only [Johnson.Unfolds.mergeSort_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
theorem below_C_bent : ¬ ((([7, 14, 20, 30] : List Nat).all fun r =>
    decide (r < keyThree.C.plan.plan.rounds.length)) = true) := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem roots_C_bent : ¬ (Johnson.Unfolds.rootsC keyThree.C.plan.plan.rounds
    [7, 14, 20, 27] = true) := by
  decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.offset_C_bent
#print axioms Johnson.AtFull.KeyBack.rounds_C_bent
#print axioms Johnson.AtFull.KeyBack.below_C_bent
#print axioms Johnson.AtFull.KeyBack.roots_C_bent
