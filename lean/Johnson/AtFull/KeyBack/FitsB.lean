-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/FitsB.lean: THE SHARED CHAIN FITS, AT THE WRITTEN VALUES. Closed facts, by
the kernel.

  `masksB`: the masks that the shared chain's folds send themselves (`ownMasks`,
    Johnson/G/RoundsOfPlan.lean), at the written codes, shape and rounds.
  `rounds_B`: the chain's trees' rounds, these masks' among them: eleven numbers.
  `fits_B`: `ChainFits keySends1 keyThree.B.plan.plan masksB 0` (TreesKOfRounds.lean).
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

/-- The masks that the shared chain's folds send themselves, at the written values. -/
abbrev masksB : List Sent :=
  ownMasks keySends1.codes keyFull.once.shape keyThree.B.plan.plan.rounds

/-- The shared chain's trees' rounds. -/
theorem rounds_B :
    roundsOfChain keySends1 0 masksB = [1, 4, 4, 17, 25, 32, 39, 44, 49, 56, 63] := by
  unfold roundsOfChain
  simp only [Johnson.Unfolds.mergeSort_eq]
  decide +kernel

theorem fits_B : ChainFits keySends1 keyThree.B.plan.plan masksB 0 :=
  ⟨by decide +kernel, sent_keySends1 "" 0,
    by rw [rounds_B]; decide +kernel, by rw [rounds_B]; decide +kernel⟩

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.rounds_B
#print axioms Johnson.AtFull.KeyBack.fits_B
