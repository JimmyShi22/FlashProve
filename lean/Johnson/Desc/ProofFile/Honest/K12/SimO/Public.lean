-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at the proximity test on G_omega: the public facts at the written place.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/Public.lean: AT THE WRITTEN PLACE `piOFull`, BY LEAN's KERNEL: the library's test `planB` and `reachTB` say no at the place, so its sentence is empty there; `reachTB` says yes at the renumbered place `renumP` (K12/Own/Renumber.lean), which has the place's numbers of positions by round.

  `plan_no_at_place`       `planB` and `reachTB` say no at `piOFull`
  `reach_renum_written`    `reachTB` at `renumP piOFull`
  `positions_renum_written`   the renumbered place declares as many positions by round as the place
  `rounds_written`         the count of rounds behind the first fold

Limits. Facts on written values alone. `planOB` at the place is the library's `planOB_O_full`. Nothing on a state of a run. No property of the protocol is claimed.
-/
import AtFullSide.K12.RestTiesAtWL
import Johnson.Desc.ProofFile.Honest.K12.Sim.FirstPubOwnAtHead
import Johnson.Desc.ProofFile.Honest.K12.Own.PlanOwn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K12
open VerifiableInference.Desc.K12 (P12 guardedProximityTestParts)
open H2K.Member (piOFull codesFull)
open H2K.JointK (laidOf laidS)
open Johnson.Prover.Link
open ProofFile.Honest.K12.Own (renumP)

theorem plan_no_at_place : (planB piOFull codesFull 3 == false && reachTB piOFull == false) = true := by
  decide +kernel

theorem reach_renum_written : reachTB (renumP piOFull) = true := by
  decide +kernel

theorem positions_renum_written :
    ((laidOf (renumP piOFull)).map (·.1)).map (·.entry.poss) =
      ((laidOf piOFull).map (·.1)).map (·.entry.poss) := by
  decide +kernel

theorem rounds_written :
    restLen piOFull.nums.stages = 2 + lenFrom (stN piOFull) (piOFull.nums.stages.drop 2) := by
  decide +kernel

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.plan_no_at_place
#print axioms ProofFile.Honest.K12.reach_renum_written
#print axioms ProofFile.Honest.K12.positions_renum_written
#print axioms ProofFile.Honest.K12.rounds_written
