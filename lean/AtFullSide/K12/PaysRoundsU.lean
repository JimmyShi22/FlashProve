-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/PaysRoundsU.lean: the written block at the test on G_u has the rounds of the test's two parts. An evaluation in Lean's kernel over the written description:
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
/-- **The written block at the test on G_u has the two parts' rounds.** -/
theorem rounds_at_U : (WP.shared.blocksInOrder.all fun b => !(b.place == placeU) ||
    b.rounds.length == firstLen piUFull.nums.stages + restLen piUFull.nums.stages) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The record has two stages or more. -/
theorem two_stages_U : 2 ≤ piUFull.nums.stages.length := by decide +kernel


end AtFullSide.K12

#print axioms AtFullSide.K12.rounds_at_U
#print axioms AtFullSide.K12.two_stages_U
