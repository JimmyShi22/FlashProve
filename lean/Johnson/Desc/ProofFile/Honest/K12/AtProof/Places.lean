-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/Places.lean: the proof file's four proximity tests (the
kind K12): each place's numbers (`P12`) by the calls by which the description's own seats make them,
of the public part. No number is typed here but the four places. Definitions with code, statements
and proofs.

  `placeU`, `placeO`, `placeW`, `placeL`   the four places: the test on the folded row's group and
                 the test on Omega's group, in the shared chain; the request's own test, in the last
                 chain; the last group's test, in the first chain
  `Four`, `fourOf`, `four`   the four places' numbers: of the planner's four records; of the public
                 part. Omega's test is an option, as in the planner's records
  `p12At_place`  the maker of a place's numbers keeps the place that it is handed
  `tests_four`   the shared chain's two tests, as the library's own seat lists them
                 (`Seat.tests`, Johnson/Desc/K12/Seat/Fill.lean), are the kind's block at
                 `Four.U` and at `Four.O`, each in its seat
  `four_L`       `Four.L` is what the first chain's lot lays (`H2U.p12OfMade`,
                 Johnson/Desc/K12/AtPlan.lean; the lot: Johnson/Desc/ProofFile/Lot/K12.lean)

Why not the written places. The library's written literals of these places
(Johnson/Desc/K12/Law/PlacesSmall.lean, PlacesFull.lean) give the shared chain's two tests the
pieces 0 and 1. The description seats them at the pieces 9 and 10. A half stands at a place, so a
job that took its numbers off such a literal would stand at no place of its chain.

Limits. The maker of a place's numbers is total: where the planner's record gives no oracle
messages, or names another chain, it yields the empty numbers (`H2U.noP12`: no stage), and `four`
still returns them: whoever lays a job asks for two stages or more. That the last chain's seat makes
its block at `Four.W` is read at its text (`P2Third.secondSeatOf`,
Johnson/Desc/ProofFile/Lot/LastChain.lean) and is not shown here. That the description's shared
chain is made of `Seat.tests` at the same planner's records is read at `Desc.K14.sharedSeatAt`
(Johnson/Desc/ProofFile/Lot/K14SeatAtZ.lean) and is not shown here. Nothing on completeness, on
soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Lot.K14SeatAtZ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K12 (P12 proximityTestKind guardedProximityTestParts)

/-- The test on the folded row's group: the shared chain's piece 9. -/
def placeU : Place := ⟨2, none, 9, .K12⟩
/-- The test on Omega's group: the shared chain's piece 10. -/
def placeO : Place := ⟨2, none, 10, .K12⟩
/-- The request's own test: the last chain's piece 2. -/
def placeW : Place := ⟨3, none, 2, .K12⟩
/-- The last group's test: the first chain's closing, piece 2. -/
def placeL : Place := ⟨1, none, 2, .K12⟩

/-- The four places' numbers. -/
structure Four where
  U : P12
  O : Option P12
  W : P12
  L : P12

/-- Of the planner's four records. -/
def fourOf (N : H2U.Places4) : Four :=
  ⟨H2U.proximityTestParametersAt placeU N.U, N.O.map (H2U.proximityTestParametersAt placeO), H2U.proximityTestParametersAt placeW N.W, H2U.proximityTestParametersAt placeL N.L⟩

/-- **Of the public part.** Nothing where the planner's records give no places. -/
def four (Z : Pub) : Option Four :=
  match H2U.placesOfMade Z.made with
  | .ok N => some (fourOf N)
  | .error _ => none

/-- The maker of a place's numbers keeps the place. -/
theorem p12At_place (a : Place) (x : H2U.PlaceNums) : (H2U.proximityTestParametersAt a x).place = a := by
  unfold H2U.proximityTestParametersAt
  split
  · rfl
  · split <;> rfl

/-- **The shared chain's two tests are the kind's block at these numbers.** -/
theorem tests_four (N : H2U.Places4) :
    VerifiableInference.Desc.K12.Seat.tests N =
      VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts (fourOf N).U) ::
        (fourOf N).O.toList.map fun p =>
          VerifiableInference.Desc.K12.Seat.onGomega (proximityTestKind guardedProximityTestParts p) := by
  unfold VerifiableInference.Desc.K12.Seat.tests fourOf
  cases N.O <;> rfl

/-- `Four.L` is `H2U.p12OfMade` at the public part's planner's record: the numbers at which, by its
text, the first chain's lot of the kind lays its block. -/
theorem four_L (Z : Pub) (F : Four) (h : four Z = some F) : F.L = H2U.p12OfMade Z.made := by
  unfold four at h
  unfold H2U.p12OfMade
  cases hN : H2U.placesOfMade Z.made with
  | error e =>
    rw [hN] at h
    cases h
  | ok N =>
    rw [hN] at h
    obtain rfl := Option.some.inj h
    rfl

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.p12At_place
#print axioms ProofFile.Honest.K12.AtProof.tests_four
#print axioms ProofFile.Honest.K12.AtProof.four_L
#print axioms ProofFile.Honest.K12.AtProof.placeU
#print axioms ProofFile.Honest.K12.AtProof.placeO
#print axioms ProofFile.Honest.K12.AtProof.placeW
#print axioms ProofFile.Honest.K12.AtProof.placeL
#print axioms ProofFile.Honest.K12.AtProof.Four
#print axioms ProofFile.Honest.K12.AtProof.fourOf
#print axioms ProofFile.Honest.K12.AtProof.four
