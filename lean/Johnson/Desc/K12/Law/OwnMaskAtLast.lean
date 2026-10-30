-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Law/OwnMaskAtLast.lean: two small facts on the proximity test (the kind K12) at its
place on the proof file's first chain, at the numbers H2U.p12OfMade m
(Johnson/Desc/K12/AtPlan.lean): its first fold sends no mask of its own, at every m; and the kind's
sub-protocol passes its test on the list of rounds (planOk) where the lot's own sub-protocol does.
Statements and proofs.

Main names:
  `placesOfMade_own`, `p12At_own`: the maker of the four places
    (Johnson/Desc/K12/Plan/PlaceOfPlan.lean) lays ownMask := false at the first chain's place, as a
    literal of its text; the place's numbers are the maker's, or those of noP12, which has false
    too.
  `p12OfMade_own`: (H2U.p12OfMade m).nums.ownMask = false, at every m. No premise.
  `planOk_of_retype`: where (atFinish π).retype passes its test on the list of rounds, proximityTestKind guardedProximityTestParts
    π passes its own: by the text of Block.retype (Johnson/Desc/Block.lean) and atFinish_planOk
    (Johnson/Desc/K12/SeatLaws.lean).
Limits: the first fact holds also where m gives no numbers (noP12): it says nothing on whether the
place's numbers are the maker's. No soundness is claimed, and nothing is said on hiding.
What each theorem rests on is printed at the file's end.

-/
import Johnson.Desc.K12.AtPlan
import Johnson.Desc.K12.SeatLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K.Made

open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- The maker of the four places lays ownMask := false at the first chain's place. -/
theorem placesOfMade_own {m : Johnson.G.OfPlan.Made} {Ps : H2U.Places4}
    (h : H2U.placesOfMade m = .ok Ps) : Ps.L.nums.ownMask = false := by
  unfold H2U.placesOfMade at h
  simp only [bind, Except.bind] at h
  repeat' split at h
  all_goals first
    | (cases h; rfl)
    | cases h

/-- The place's numbers are the maker's, or those of noP12. -/
theorem p12At_own (place : Place) (x : H2U.PlaceNums) (h : x.nums.ownMask = false) :
    (H2U.proximityTestParametersAt place x).nums.ownMask = false := by
  unfold H2U.proximityTestParametersAt
  split
  · rfl
  · split
    · exact h
    · rfl

/-- **The first fold of the first chain's test sends no mask of its own**, at every m. -/
theorem p12OfMade_own (m : Johnson.G.OfPlan.Made) : (H2U.p12OfMade m).nums.ownMask = false := by
  unfold H2U.p12OfMade
  dsimp only
  split
  · rename_i Ps h
    exact p12At_own _ _ (placesOfMade_own h)
  · rfl

/-- From the lot's own sub-protocol's test on the list of rounds to the kind's. -/
theorem planOk_of_retype {Cl : Type} (π : P12)
    (h : ((atFinish π).retype : Block First.S Cl).planOk = true) :
    (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true := by
  have h' : ((atFinish π).planOk && (atFinish π).claims.isEmpty) = true := h
  exact VerifiableInference.Desc.K12.Seat.atFinish_planOk π (Bool.and_eq_true_iff.1 h').1

end H2K.Made

#print axioms H2K.Made.p12OfMade_own
#print axioms H2K.Made.planOk_of_retype
