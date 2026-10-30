-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Told/Reads.lean: the fit's «reads» for every description whose further
  reading is VerifierAndGoals.readMoreAt recordGround (Ladder/ReadThru.lean)
  against the public algorithm pub8
(Johnson/Top/PreThreePub.lean). Stated of the algorithm's own term, naming no description: at such a
  description VerifierAndGoals.Fit.readBoth … Prod.mk (Johnson/PV/Fit.lean) is that term by unfolding.
  **reads_pub8**        «readConfig Z, then readMoreAt recordGround Z c, then (c, m)» returns at
    every hash function what pub8 recordGround Z.pol Z.KL Z.lay returns at it
  «hq₀» (queryBound_askListL · within8_pub8) stands in
    Johnson/Goal/Conditions/ToldReadsWithin.lean, which this file imports: so whoever imports this
    file has all three names, each declared once.
After reads_describe | hq₀_describe (Johnson/PV/Describe.lean), which speak of that file's own
  askList; here Ladder/ReadThru.lean's is taken by name: no third askList is typed.
Who reads each letter. Z: its three files go into the eight strings. hash: asked at these strings
  alone. No ∃.
Does not show. That the eight strings are what a program hashes (readConfig_thru |
  readMoreAt_thru, Johnson/Goal/Tie/ReadThruHead.lean, say it of the running head). Nothing on
  soundness. No verifier is named: the silly members have nothing to meet.
No soundness is claimed.
-/
import Ladder.ReadThru
import Johnson.PV.Fit
import Johnson.Goal.Conditions.ToldReadsWithin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifierAndGoals.Told
open VerifierAndGoals VerifiableInference VerifiableInference.OnPublicFiles Rom
open OnBytes.K.Arm.Pub OnBytes.Tie

/-- **«reads».** -/
theorem reads_pub8 (Z : PublicFiles) (hash : VerifiableInference.Hash) :
    ((readConfig Z).andThen fun c => (readMoreAt recordGround Z c).andThen fun m =>
      (.done (c, m) : DeterministicAlgorithm D8)).evaluate hash =
      (pub8 recordGround Z.pol Z.KL Z.lay).det fun _ => hash := by
  rw [pub8_det, DeterministicAlgorithm.evaluate_andThen, DeterministicAlgorithm.evaluate_andThen]
  show (_, (askList _).evaluate hash) = _
  rw [evaluate_askList]
  rfl

end VerifierAndGoals.Told

#print axioms VerifierAndGoals.Told.reads_pub8
