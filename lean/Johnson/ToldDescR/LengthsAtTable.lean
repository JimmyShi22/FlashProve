-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/LengthsAtTable.lean: no soundness is claimed.
The second and the third of the three lengths that tablesGlued asks (Johnson/Desc/Sound/TablesGlued.lean: 1 + T.l₂.length = (sharedPlaces split).length · 1 + T.l₃.length = lastPlaces.length), to the sign, at every description F that onlineDescription makes and every T whose pieces hold F's own blocks (OfDesc F T, Johnson/Desc/Sound/DescThree.lean:76-88).
  len₁ | len₂ | len₃_of_ofDesc   general in F: a rule's pieces are as many as the chain's flat list's blocks (OfDesc's b₁ | b₂ | b₃, by length)
  **third_length**     onlineDescription … = .ok F → OfDesc F T → 1 + T.l₃.length = lastPlaces.length: no other premise
  **second_length**    … → F.planOk = true → ∃ Z N, the road has made Z · placesOfMade Z.made = .ok N · 1 + T.l₂.length = (sharedPlaces N.O.isSome).length
Who reads each letter. T: through OfDesc alone. ∃ Z N: as in PlacesAtTable.lean: each with the equation that fixes it.
Does not show. The first length (ps is a letter of the first chain's table): len₁_of_ofDesc carries it to F.first.blocksInOrder.length. Nothing on soundness.
-/
import Johnson.ToldDescR.PlacesAtTable
import Johnson.Desc.Sound.DescThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open ProofFile
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.Sound (OfDesc ThreeAt)
open VerifiableInference.Desc.Shared (sharedPlaces)
open VerifiableInference.Desc.Last (lastPlaces)
open OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)

section
variable {C : CK} {D : WholeD} {all : List LeftT} {Xi X₁ X₂ W : Type} {F : FileDescription Xi}
  {T : ThreeAt C D all F X₁ X₂ W}

theorem len₁_of_ofDesc (h : OfDesc F T) : 1 + T.l₁.length = F.first.blocksInOrder.length := by
  have e := congrArg List.length h.b₁
  simp only [List.length_map, List.length_cons] at e
  omega

theorem len₂_of_ofDesc (h : OfDesc F T) : 1 + T.l₂.length = F.shared.blocksInOrder.length := by
  have e := congrArg List.length h.b₂
  simp only [List.length_map, List.length_cons] at e
  omega

theorem len₃_of_ofDesc (h : OfDesc F T) : 1 + T.l₃.length = F.second.blocksInOrder.length := by
  have e := congrArg List.length h.b₃
  simp only [List.length_map, List.length_cons] at e
  omega

end

section
variable {C : CK} {D : WholeD} {all : List LeftT} {X₁ X₂ W : Type} {o : ProofFile.SecondHashFunctionArgument}
  {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {T : ThreeAt C D all F X₁ X₂ W}

/-- **The third length.** -/
theorem third_length (h : onlineDescription o pol lay KL = .ok F) (hT : OfDesc F T) :
    1 + T.l₃.length = lastPlaces.length :=
  (len₃_of_ofDesc hT).trans (last_fits_descPure h).2

/-- **The second length**, under the tests on the plan. -/
theorem second_length (h : onlineDescription o pol lay KL = .ok F) (hp : F.planOk = true) (hT : OfDesc F T) :
    ∃ (Z : ProofFile.Pub) (N : H2U.Places4), pureRoad.pub o pol lay KL = .ok Z ∧
      H2U.placesOfMade Z.made = .ok N ∧ 1 + T.l₂.length = (sharedPlaces N.O.isSome).length := by
  obtain ⟨Z, N, hZ, hN, -, hl⟩ := shared_fits_descPure h hp
  exact ⟨Z, N, hZ, hN, (len₂_of_ofDesc hT).trans hl⟩

end

end ToldDesc

#print axioms ToldDesc.len₁_of_ofDesc
#print axioms ToldDesc.third_length
#print axioms ToldDesc.second_length
