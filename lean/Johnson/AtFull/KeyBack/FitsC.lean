-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/FitsC.lean: THE SECOND CHAIN FITS, AT THE WRITTEN VALUES. Closed facts, by
the kernel.

  `rounds_C`: the chain's trees' rounds: [7, 14, 20, 26].
  `fits_C`: `ChainFits keySends2 keyThree.C.plan.plan [] 0` (TreesKOfRounds.lean).
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

/-- The second chain's trees' rounds. -/
theorem rounds_C : roundsOfChain keySends2 0 [] = [7, 14, 20, 26] := by
  unfold roundsOfChain
  simp only [Johnson.Unfolds.mergeSort_eq]
  decide +kernel

theorem fits_C : ChainFits keySends2 keyThree.C.plan.plan [] 0 :=
  ⟨by decide +kernel, sent_keySends2 "" 0,
    by rw [rounds_C]; decide +kernel, by rw [rounds_C]; decide +kernel⟩

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.rounds_C
#print axioms Johnson.AtFull.KeyBack.fits_C
