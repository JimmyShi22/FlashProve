-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/RangesLinesKernel.lean: the closed lines of the key file's
test on the ranges at its written place piKRFull, by the kernel's own evaluation. The tests are
those of RangesLinesGuards.lean.

  seeds_KR      the round that sends the test's tree τ, for τ below 3
  roots_KR      the test's rounds count three roots or more
  opened_KR     what the test opens of older trees: tree number 1 alone, at the sending's width
  opened_wide, opened_late   controls: at one word more, or with three trees in front, no
  seeds_late    control: no tree is sent one round later
  count_KR, len_KR, hk_KR   the test states one oracle message fewer than it has stages; it has
                four stages; h ≤ k at each

Limits. Public numbers at piKRFull. Some of that place's numbers rest on a print: the limits of
Johnson/Desc/K12/Law/PlaceKeyRangesFull.lean; in scope it is held against the description by
place_sourced (E2E/KeyRangesK12.lean). Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.RangesLinesGuards

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open VerifiableInference.Desc (Block sendRound)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open H2K.Member (piKRFull)
open AtPublicFiles.KeyThread (rootsOf)

theorem seeds_KR : ∀ τ, τ < 3 →
    sendRound (proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).rounds τ =
      some (seedRound piKRFull.nums.stages τ) := by
  decide +kernel

theorem seeds_late : ∀ τ, τ < 3 →
    sendRound (proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).rounds τ ≠
      some (seedRound piKRFull.nums.stages τ + 1) := by
  decide +kernel

theorem roots_KR : 3 ≤ rootsOf (proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).rounds := by
  decide +kernel

theorem opened_KR : oldOpensB piKRFull msgWords 2 = true := by decide +kernel

theorem opened_wide : oldOpensB piKRFull (msgWords + 1) 2 = false := by decide +kernel

theorem opened_late : oldOpensB piKRFull msgWords 3 = false := by decide +kernel

theorem count_KR : ((proximityTestKind guardedProximityTestParts piKRFull : Block T12 Unit).oracles.flatMap id).length + 1 =
    piKRFull.nums.stages.length := by
  decide +kernel

theorem len_KR : piKRFull.nums.stages.length = 4 := by decide +kernel

theorem hk_KR : ∀ a ∈ piKRFull.nums.stages, a.h ≤ a.k := by decide +kernel

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.seeds_KR
#print axioms ProofFile.Honest.K12.AtKey.seeds_late
#print axioms ProofFile.Honest.K12.AtKey.roots_KR
#print axioms ProofFile.Honest.K12.AtKey.opened_KR
#print axioms ProofFile.Honest.K12.AtKey.opened_wide
#print axioms ProofFile.Honest.K12.AtKey.opened_late
#print axioms ProofFile.Honest.K12.AtKey.count_KR
#print axioms ProofFile.Honest.K12.AtKey.len_KR
#print axioms ProofFile.Honest.K12.AtKey.hk_KR
