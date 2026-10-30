-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/SharedPlaces.lean: no soundness is claimed.
The shared chain's flat list stands at the places of the shared chain's table (sharedPlaces split, Johnson/Desc/Shared/BordersShared.lean:123-127), at the seat that onlineDescription lays: by make, where kind K14's eight blocks can be said (Desc.K14.blocks P returns). split := «the plan has a second test on the shared chain» (N.O.isSome).
Where blocks P does not return the seat lays one block in the eight's stead, whose test on the plan says no (blocksOr, Johnson/Desc/K14/Blocks.lean:201-204): the places are then others, and F.planOk is false: `eight_of_planOk` says so: so under the chain's blocks' tests on the plan the premise is paid.
The list is written out here (sharedList), so that this file does not import Johnson/Desc/Shared/BordersShared.lean: sharedPlaces is that list to the sign: «rfl» at the caller.
  blocks_places         blocks P = some l → l.map (·.place) = the eight places 1 … 8
  tests_places          the one or two proximity tests stand at 9 (and 10)
  places_chainOf        (Desc.K14.chainOf c P ts last).blocksInOrder.map (·.place), from the places of blocksOr P, ts and last
  **shared_places**     laterShared Z = some A → placesOfMade Z.made = .ok N → blocks ‹its P› = some l → A.chain.blocksInOrder.map (·.place) = sharedList N.O.isSome
  shared_links          laterShared Z = some A → A.chain.links = []: so Chain.retype's laws reach it
  eight_of_planOk       if every block of blocksOr P passes its test on the plan, blocks P returns
The seat is that of Johnson/Desc/ProofFile/Lot/K14SeatAtZ.lean (sharedSeatAt · beforePointOf).
Who reads each letter. Z: the seat's maker; the places hang on N.O.isSome alone. l: fixed by its equation.
Does not show. That N.O.isSome is the shape's «sharedSplitNeeded». That the pieces' lists of a rule are as long as the flat lists. Nothing on soundness.
-/
import Johnson.ToldDescR.LastPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open ProofFile
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open Desc.K14 (blocks blocksOr frontBlock P14 St p14Of sharedSeatOf beforePointOf)

/-- The places of the shared chain's flat list. -/
def sharedList (split : Bool) : List Place :=
  [⟨2, none, 0, .frame⟩, ⟨2, none, 1, .K14⟩, ⟨2, none, 2, .K1⟩, ⟨2, none, 3, .K14⟩,
   ⟨2, none, 4, .K14⟩, ⟨2, none, 5, .K1⟩, ⟨2, none, 6, .K14⟩, ⟨2, none, 7, .K14⟩,
   ⟨2, none, 8, .K14⟩, ⟨2, none, 9, .K12⟩] ++
    (if split then [⟨2, none, 10, .K12⟩] else []) ++ [⟨2, none, 11, .frame⟩]

/-- The eight blocks' places. -/
theorem blocks_places {P : P14} {l : List (Block St Unit)} (h : blocks P = some l) :
    l.map (·.place) =
      [⟨2, none, 1, .K14⟩, ⟨2, none, 2, .K1⟩, ⟨2, none, 3, .K14⟩, ⟨2, none, 4, .K14⟩,
       ⟨2, none, 5, .K1⟩, ⟨2, none, 6, .K14⟩, ⟨2, none, 7, .K14⟩, ⟨2, none, 8, .K14⟩] := by
  unfold blocks at h
  cases hu : Desc.K14.withU P.S with
  | none =>
    simp only [hu] at h
    exact nomatch h
  | some u =>
    simp only [hu] at h
    have e := Option.some.inj h
    rw [← e]
    rfl

/-- The one or two proximity tests' places. -/
theorem tests_places (N : H2U.Places4) :
    (VerifiableInference.Desc.K12.Seat.tests N).map (·.place) =
      ⟨2, none, 9, .K12⟩ :: (if N.O.isSome then [⟨2, none, 10, .K12⟩] else []) := by
  unfold VerifiableInference.Desc.K12.Seat.tests
  have k : ∀ (pl : Place) (x : H2U.PlaceNums),
      (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts (H2U.proximityTestParametersAt pl x) :
        Block VerifiableInference.Desc.K12.T12 Unit).place = pl := fun pl x =>
    (k12_place _ _).trans (p12At_place _ _)
  cases hO : N.O with
  | none =>
    show [(VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
      (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U) : Block VerifiableInference.Desc.K12.T12 Unit).place] = _
    rw [k]
    rfl
  | some nO =>
    show [(VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
        (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U) : Block VerifiableInference.Desc.K12.T12 Unit).place,
      (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
        (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) : Block VerifiableInference.Desc.K12.T12 Unit).place] = _
    rw [k, k]
    rfl

/-- The shared chain's flat list's places, from its parts'. -/
theorem places_chainOf (c : OnBytes.Model.Verify.Chains) (P : P14) (ts : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit) :
    (Desc.K14.chainOf c P ts last).blocksInOrder.map (·.place) =
      ⟨2, none, 0, .frame⟩ :: ((blocksOr P).map (·.place) ++ ts.map (·.place) ++
        [(last (blocksOr P ++ ts)).place]) := by
  unfold Desc.K14.chainOf Chain.blocksInOrder
  simp only [List.map_cons, List.map_nil, List.flatMap_nil, List.append_nil, List.map_append,
    List.map_map, List.cons_append, List.nil_append]
  rfl

/-- **The shared chain's flat list stands at the table's places.** -/
theorem shared_places {Z : ProofFile.Pub} {A : SharedSeat} {N : H2U.Places4}
    (h : laterShared Z = some A) (hN : H2U.placesOfMade Z.made = .ok N)
    {l : List (Block St Unit)} (hl : blocks (p14Of Z.p.chains (beforePointOf N)) = some l) :
    A.chain.blocksInOrder.map (·.place) = sharedList N.O.isSome := by
  unfold laterShared Desc.K14.sharedSeatAt at h
  rw [hN] at h
  have e := Option.some.inj h
  subst e
  show (Desc.K14.chainOf Z.p.chains (p14Of Z.p.chains (beforePointOf N))
    (VerifiableInference.Desc.K12.Seat.tests N) VerifiableInference.Desc.K12.Seat.last).blocksInOrder.map
      (·.place) = _
  rw [places_chainOf, tests_places]
  unfold blocksOr
  rw [hl, Option.getD_some, blocks_places hl]
  cases N.O.isSome <;> rfl

/-- The shared chain's seat has no link. -/
theorem shared_links {Z : ProofFile.Pub} {A : SharedSeat} (h : laterShared Z = some A) :
    A.chain.links = [] := by
  unfold laterShared Desc.K14.sharedSeatAt at h
  split at h
  · have e := Option.some.inj h
    subst e
    rfl
  · exact nomatch h

/-- If every block that the seat lays for the eight passes its test on the plan, the eight can be
said. -/
theorem eight_of_planOk {P : P14} (h : (blocksOr P).all (·.planOk) = true) :
    ∃ l, blocks P = some l := by
  cases hb : blocks P with
  | some l => exact ⟨l, rfl⟩
  | none =>
    unfold blocksOr at h
    rw [hb] at h
    exact nomatch h

end ToldDesc

#print axioms ToldDesc.blocks_places
#print axioms ToldDesc.tests_places
#print axioms ToldDesc.places_chainOf
#print axioms ToldDesc.shared_places
#print axioms ToldDesc.shared_links
#print axioms ToldDesc.eight_of_planOk
