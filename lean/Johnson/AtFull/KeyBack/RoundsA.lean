-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/RoundsA.lean: THE FIRST CHAIN's TREES' ROUNDS, AT THE WRITTEN VALUES. One
closed fact, by the kernel.

`rounds_A`: `roundsOfChain keySends0 1 []` (RoundsOfSent.lean) is [0, 2, 18811, 18818, 18824,
18848]. At a `List.mergeSort` like the one inside it the kernel was seen to stop (at the second
chain's list). So the sort is first rewritten, by `mergeSort_eq` (Johnson/Unfolds/MergeSort.lean),
into a form that the kernel can evaluate; then `decide +kernel`.
Limits. It names no m and no public file: that the written values are the planner's at any public
files is not said here. Nothing on soundness, nothing on hiding.

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

/-- The first chain's trees' rounds. -/
theorem rounds_A : roundsOfChain keySends0 1 [] = [0, 2, 18811, 18818, 18824, 18848] := by
  unfold roundsOfChain
  simp only [Johnson.Unfolds.mergeSort_eq]
  decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.rounds_A
