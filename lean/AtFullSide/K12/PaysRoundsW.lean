-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/PaysRoundsW.lean: the written block at the last chain's proximity test has the rounds of the test's two parts. An evaluation in Lean's kernel over the written description:
public data alone, the full size alone. No independent checker has replayed it. Nothing on
completeness, soundness or hiding.
-/
import Johnson.AtFull.ProofPlan.WP
import Johnson.Desc.ProofFile.Honest.K12.HalfSteps
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Places
import Johnson.Desc.K12.Law.PlacesFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open H2K.Member (piUFull piOFull piWFull piLFull)
open P2Law.ProofPlan (WP)

set_option maxRecDepth 1000000 in
/-- **The written block at the last chain's test has the two parts' rounds.** -/
theorem rounds_at_W : (WP.second.blocksInOrder.all fun b => !(b.place == placeW) ||
    b.rounds.length == firstLen piWFull.nums.stages + restLen piWFull.nums.stages) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The record has two stages or more. -/
theorem two_stages_W : 2 ≤ piWFull.nums.stages.length := by decide +kernel


end AtFullSide.K12

#print axioms AtFullSide.K12.rounds_at_W
#print axioms AtFullSide.K12.two_stages_W
