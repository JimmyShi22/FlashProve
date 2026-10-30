-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/KeyFirstVerdictNo.lean: the three tests of KeyFirstVerdict.lean CAN FAIL: at
the key file's first written plan with one thing bent, each part of the plan's verdict
(`Planned.holds`, OnBytes/Params/Planner.lean) rejects. Closed facts by evaluations in Lean's
kernel, each stated positively ("= false"). In a file of its own, which no other file imports.

  `key_rounds_bent`: the target raised by 400 bits: some round does not hold.
  `key_words_bent`: behind the last round a round whose flag `wordFault` is set: the walk reaches
    it.
  `key_distance_bent`: behind the last round a round that says the first said group's two codes
    with another integer.
Limits. Written values, bent by hand. Coarse bends: 400 bits (no edge is shown); the very flag that
the test reads: these two show only that a test can reject. No soundness is claimed.
-/
import Johnson.Goal.Numbers.KeyFirstListed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open VerifiableInference.Number.ByRuns OnBytes OnBytes.Params Johnson.G

/-- The first written plan with a round laid behind its last. -/
def keyWith (r : PlanRound) : Planned := ⟨keyThree.A.plan.set, keyThree.A.plan.rounds ++ [r]⟩

/-- The first group that the plan says, with another integer. -/
def otherChoice : Option PricedChoice :=
  (keyThree.A.plan.rounds.filterMap (·.group)).head?.map fun g => { g with m := g.m + 1 }

set_option maxRecDepth 1000000 in
theorem key_rounds_bent :
    (⟨{ keyThree.A.plan.set with target := keyThree.A.plan.set.target + 400 },
      keyThree.A.plan.rounds⟩ : Planned).roundsHold = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem key_words_bent :
    (keyWith { entry := default, wordFault := true }).wordsFit = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem key_distance_bent :
    (keyWith { entry := default, group := otherChoice }).oneDistance = false := by decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.key_rounds_bent
#print axioms Johnson.AtFull.Made.key_words_bent
#print axioms Johnson.AtFull.Made.key_distance_bent
