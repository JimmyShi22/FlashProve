--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Member/Stands.lean: at which places a member of the first chain's flat
list stands. Statements with their proofs.

The statements of Johnson/Desc/ProofFile/Honest/Member/Statement.lean speak of every member at a
place and take for a premise that one stands there. The library has the whole list of the flat
list's places as one equation, at `onlineDescription` opened as `IM.Open` has it (`IM.places_any`,
Johnson/IMR/PlacesScope.lean). Here that is said by the place.
Main names:
  `stands_iff`: **a member stands at a place just if the place is in the driver's list of the places
    of all sub-protocols of the first chain** (`flatPlacesOf`, Johnson/Desc/First/Driver/Chain.lean)
    at the sorts of the segments of the public part. For every place. The four names that follow
    are cases of it; they are proved by other laws of the library.
  `stands_first`: at the first place of segment l, of the first of the segment's hearing kinds
    (`IM.joined_at`, Johnson/IMR/SameSpot.lean).
  `stands_m3`, `stands_m4`: at "M:3" and at "M:4" (`IM.back_of`, Johnson/IMR/BackSeat.lean).
  `stands_end`: at the first chain's last place (`IM.seal_seated`, Johnson/IMR/SealSeat.lean).
  `mem_flat_of_back`: a sub-protocol behind the segments, by index, is a member of the flat list as
    `Chain.blocksInOrder` lays it.
  `find_of_stands`: where a member stands at a place, `List.find?` on the place returns one. With
    `of_find` (Honest/Member/AtLot.lean) the two go both ways.

What is not claimed. Which places the list has at a given public part: that hangs on the sorts of
its segments; in `stands_first`, which sort segment l has is a premise. That `onlineDescription` returns at
any three files. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.ProofFile.Honest.Member.AtLot
import Johnson.IMR.BackSeat
import Johnson.IMR.PlacesScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.AtPlace
open VerifiableInference.Desc (Block Chain FileDescription KindName Place)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)

/-- A sub-protocol behind the segments, by index, is a member of the flat list as `Chain.blocksInOrder` lays
it. -/
theorem mem_flat_of_back {σ C : Type} {c : Chain σ C} {j : Nat} {b : Block σ C}
    (h : c.back[j]? = some b) : { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } ∈ c.blocksInOrder := by
  unfold Chain.blocksInOrder
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.2 ⟨b, List.mem_of_getElem? h, rfl⟩))

/-- Where a member stands at a place, `List.find?` on the place returns one. -/
theorem find_of_stands {σ C : Type} {l : List (Block σ C)} {a : Place}
    (h : ∃ m ∈ l, m.place = a) : ∃ m, (l.find? fun x => x.place == a) = some m := by
  obtain ⟨m, hm, hp⟩ := h
  have hs : (l.find? fun x => x.place == a).isSome = true :=
    List.find?_isSome.2 ⟨m, hm, beq_iff_eq.2 hp⟩
  exact Option.isSome_iff_exists.1 hs

variable {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Z : Pub} {Bs : PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : SharedSeat} {B : SecondSeat}

/-- A member of the flat list stands at the first place of segment l, of the first of the segment's
hearing kinds. -/
theorem stands_first (O : IM.Open o pol lay KL F Z Bs base c A B) {l : Nat} {sub : ModelPart}
    (hl : (subsOf Z)[l]? = some sub) {k : KindName} (hk : (kindsBeforeBatching sub (l == 0))[0]? = some k) :
    ∃ m ∈ c.blocksInOrder, m.place = ⟨1, some l, 1, k⟩ := by
  obtain ⟨Lk, b, e1, e2, _, _, _, _, _, hJ⟩ := IM.joined_at O hl hk
  obtain ⟨_, _, _, _, e⟩ := hJ
  exact ⟨b, mem_flat_of_hear e1 e2, by rw [e]; rfl⟩

/-- A member of the flat list stands at "M:3". -/
theorem stands_m3 (O : IM.Open o pol lay KL F Z Bs base c A B) :
    ∃ m ∈ c.blocksInOrder, m.place = ⟨1, none, 3, .K13⟩ := by
  obtain ⟨_, _, ⟨b, _, e, _, _, hA⟩, _⟩ := IM.back_of O
  have hp : b.place = ⟨1, none, 3, .K13⟩ := IM.alone_place hA
  exact ⟨_, mem_flat_of_back e, hp⟩

/-- A member of the flat list stands at "M:4". -/
theorem stands_m4 (O : IM.Open o pol lay KL F Z Bs base c A B) :
    ∃ m ∈ c.blocksInOrder, m.place = ⟨1, none, 4, .K1⟩ := by
  obtain ⟨_, _, _, b, _, _, e, _, _, _, hA⟩ := IM.back_of O
  have hp : b.place = ⟨1, none, 4, .K1⟩ := IM.alone_place hA
  exact ⟨_, mem_flat_of_back e, hp⟩

/-- A member of the flat list stands at the first chain's last place. -/
theorem stands_end (O : IM.Open o pol lay KL F Z Bs base c A B) :
    ∃ m ∈ c.blocksInOrder, m.place = ⟨1, none, 5, .frame⟩ := by
  obtain ⟨_, _, _, hA⟩ := IM.seal_seated O
  have hp : c.last.place = ⟨1, none, 5, .frame⟩ := IM.alone_place hA
  refine ⟨{ c.last with planOk := c.last.planOk && c.last.hasNoClaimsAndNothingAfter }, ?_, hp⟩
  unfold Chain.blocksInOrder
  exact List.mem_append_right _ (List.mem_singleton.2 rfl)

/-- **A member of the flat list stands at a place just if the place is in the driver's list of the
places of all sub-protocols of the first chain** (`flatPlacesOf`), at the sorts of the segments of
the public part (`IM.places_any`, Johnson/IMR/PlacesScope.lean). -/
theorem stands_iff (O : IM.Open o pol lay KL F Z Bs base c A B) (a : Place) :
    (∃ m ∈ c.blocksInOrder, m.place = a) ↔
      a ∈ VerifiableInference.Desc.First.flatPlacesOf (subsOf Z) true := by
  rw [← IM.places_any O]
  exact List.mem_map.symm

end ProofFile.Honest.AtPlace

#print axioms ProofFile.Honest.AtPlace.mem_flat_of_back
#print axioms ProofFile.Honest.AtPlace.find_of_stands
#print axioms ProofFile.Honest.AtPlace.stands_first
#print axioms ProofFile.Honest.AtPlace.stands_m3
#print axioms ProofFile.Honest.AtPlace.stands_m4
#print axioms ProofFile.Honest.AtPlace.stands_end
#print axioms ProofFile.Honest.AtPlace.stands_iff
