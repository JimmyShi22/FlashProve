-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/LastPlaces.lean: no soundness is claimed.
The last chain's flat list has four blocks, at the four places of the last chain's table (lastPlaces, Johnson/Desc/Last/BordersLast.lean:73), at every description that onlineDescription makes: by make. So the third of the three lengths that tablesGlued asks (1 + T.l₃.length = lastPlaces.length) is a fact on the flat list, and placesFitS c lastPlaces says yes.
The list is written out here (fourPlaces), so that this file does not import Johnson/Desc/Last/BordersLast.lean: lastPlaces is that list to the sign: «rfl» at the caller.
  p12At_place | k12_place | onOwn_place   a proximity test's block stands at the place that it is handed
  places_tiedEnd        (lastChainWithOwnTest p own).blocksInOrder.map (·.place), at every p and own
  **last_places**       laterSecond Z = some B → B.chain.blocksInOrder.map (·.place) = fourPlaces
  last_links            … → B.chain.links = []: so Chain.retype's laws (Retype.lean) reach it
  last_length           … → B.chain.blocksInOrder.length = 4
  **last_places_descPure**   at every F that onlineDescription makes: F.second.blocksInOrder.map (·.place) = fourPlaces
The seat is that of Johnson/Desc/ProofFile/Lot/LastChain.lean; the chain has its first and last block as fields (Johnson/Desc/Third/Chain.lean); the frame lays the seat's chain by Chain.retype: the last theorem goes through places_retype; onlineDescription takes the letter o.
Who reads each letter. Z: the seat's maker alone; the places hang on nothing of it. No ∃ but in the last theorem's proof.
Does not show. That the pieces' lists of a rule are as long as the flat lists (the cutting's law: another file's). Nothing on what the blocks do. Nothing on soundness.
-/
import Johnson.ToldDescR.Reads
import Johnson.ToldDescR.Retype

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open ProofFile
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.Third (lastChainWithOwnTest S₃ P₁₄)

/-- The four places of the last chain's flat list. -/
def fourPlaces : List Place :=
  [⟨3, none, 0, .K14⟩, ⟨3, none, 1, .frame⟩, ⟨3, none, 2, .K12⟩, ⟨3, none, 3, .frame⟩]

theorem p12At_place (pl : Place) (x : H2U.PlaceNums) : (H2U.proximityTestParametersAt pl x).place = pl := by
  unfold H2U.proximityTestParametersAt
  split
  · rfl
  · split <;> rfl

theorem k12_place {T Cl : Type} (X : VerifiableInference.Desc.K12.Parts T)
    (p : VerifiableInference.Desc.K12.P12) :
    (VerifiableInference.Desc.K12.proximityTestKind X p : Block T Cl).place = p.place := by
  unfold VerifiableInference.Desc.K12.proximityTestKind
  split <;> rfl

/-- The last chain's flat list's places, at every argument. -/
theorem places_tiedEnd {Cl : Type} (p : P₁₄) (own : Block S₃ Cl) :
    (lastChainWithOwnTest p own).blocksInOrder.map (·.place) =
      [⟨3, none, 0, .K14⟩, ⟨3, none, 1, .frame⟩,
        { own.place with chain := 3, link := none, piece := 2 }, ⟨3, none, 3, .frame⟩] := rfl

/-- **The last chain's flat list stands at the table's four places.** -/
theorem last_places {Z : ProofFile.Pub} {B : SecondSeat} (h : laterSecond Z = some B) :
    B.chain.blocksInOrder.map (·.place) = fourPlaces := by
  unfold laterSecond P2Third.secondSeat at h
  split at h
  · have e := Option.some.inj h
    subst e
    refine (places_tiedEnd _ _).trans ?_
    have k : ∀ N : H2U.PlaceNums, (VerifiableInference.Desc.K12.Seat.onOwn
        (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
          (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N) : Block _ Unit)).place = ⟨3, none, 2, .K12⟩ := fun N => by
      show (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
        (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N) : Block VerifiableInference.Desc.K12.T12 Unit).place = _
      exact (k12_place _ _).trans (p12At_place _ _)
    rw [k]
    rfl
  · exact nomatch h

/-- The last chain's seat has no link. -/
theorem last_links {Z : ProofFile.Pub} {B : SecondSeat} (h : laterSecond Z = some B) :
    B.chain.links = [] := by
  unfold laterSecond P2Third.secondSeat at h
  split at h
  · have e := Option.some.inj h
    subst e
    rfl
  · exact nomatch h

theorem last_length {Z : ProofFile.Pub} {B : SecondSeat} (h : laterSecond Z = some B) :
    B.chain.blocksInOrder.length = 4 := by
  have e := congrArg List.length (last_places h)
  rwa [List.length_map] at e

/-- **At every description that `onlineDescription` makes.** -/
theorem last_places_descPure {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : onlineDescription o pol lay KL = .ok F) : F.second.blocksInOrder.map (·.place) = fourPlaces := by
  obtain ⟨Z, -, h⟩ := ProofFile.Law.descPure_made h
  obtain ⟨A, B, c, -, hB, rfl⟩ := pureZ_make h
  have hB' : laterSecond Z = some B := hB
  exact (places_retype B.chain (last_links hB')).trans (last_places hB')

end ToldDesc

#print axioms ToldDesc.places_tiedEnd
#print axioms ToldDesc.last_places
#print axioms ToldDesc.last_links
#print axioms ToldDesc.last_length
#print axioms ToldDesc.last_places_descPure
