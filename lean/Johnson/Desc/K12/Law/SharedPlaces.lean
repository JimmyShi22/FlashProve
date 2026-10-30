-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.SitsChains
/-
Johnson/Desc/K12/Law/SharedPlaces.lean: THE PLACES OF THE SHARED CHAIN's FLAT LIST, AS FAR AS THEY ARE THE PROXIMITY TEST's AND ITS SEAT's: for the field «the real shared chain's flat list has the table's places» (placesFitS … (sharedPlaces split), Johnson/Desc/Shared/BordersShared.lean: its two definitions are not named in the code here). BOOK-KEEPING ON THE PLAN. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  place_of_k12 · place_of_p12At      the kind's block bears its parameter's place, in both arms of its text; the maker's parameter bears the place that it is handed, in all three arms
  guEntry_place | omegaEntry_place | sharedEnd_place     ⟨2, none, 9, .K12⟩ · ⟨2, none, 10, .K12⟩ · ⟨2, none, 11, .frame⟩
  shared_places     the flat list's places = ‹the front block's› :: ‹the shared chain's own blocks'› ++ ⟨2, none, 9, .K12⟩ :: ((if N.O.isSome then [⟨2, none, 10, .K12⟩] else []) ++ [⟨2, none, 11, .frame⟩]): THE TABLE's LETTER «split» IS NOT FREE AT THE SEAT: IT IS N.O.isSome
  tests_places | tests_places_none · last_place     FOR THE SHARED CHAIN's FILES' RULE ON chainOf's PLACES (its two premises h9 | h11): (Seat.tests N).map (·.place) = [⟨2, none, 9, .K12⟩, ⟨2, none, 10, .K12⟩] where N.O = some nO ([⟨2, none, 9, .K12⟩] where none) · (Seat.last front).place = ⟨2, none, 11, .frame⟩ at every front
  retype_places · asBare_of_retype · retype_planOk   THE CARRIAGE: the chain retyped (as a description holds it) has the chain's own places; where every entry of the retyped flat list passes its test on the plan, so does every entry of the chain's own
WHAT IS NOT HERE: the nine places in front (the front block's; Desc.K14.blocksOr P's: left to the shared chain's files; blocksOr has a fall-back arm where Desc.K14.blocks P = none) · N.O against the shape's sharedSplitNeeded.
FELLOWS, BY STATEMENT (why the first two bear these names): H2K.JointK.k12_place (Johnson/Loose/H2K12/SitsInPure.lean) · IM.k12_place (Johnson/IMR/LotKinds.lean) · H2K.JointK.p12At_place (H2K12/WordAtSeats.lean [not in this library]); here they stand under names of their own, so that no full name stands twice.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12

theorem place_of_k12 {T Cl : Type} (X : Parts T) (p : P12) : (proximityTestKind X p : Block T Cl).place = p.place := by
  unfold proximityTestKind
  split <;> rfl

theorem place_of_p12At (place : Place) (x : H2U.PlaceNums) : (H2U.proximityTestParametersAt place x).place = place := by
  unfold H2U.proximityTestParametersAt
  split
  · rfl
  · split <;> rfl

theorem guEntry_place (Cl' : Type) (N : H2U.Places4) :
    (guEntry Cl' N).place = ⟨2, none, 9, .K12⟩ := by
  show (proximityTestKind guardedProximityTestParts (pGu N) : Blk').place = _
  rw [place_of_k12]
  exact place_of_p12At _ _

theorem omegaEntry_place (Cl' : Type) (nO : H2U.PlaceNums) :
    (omegaEntry Cl' nO).place = ⟨2, none, 10, .K12⟩ := by
  show (proximityTestKind guardedProximityTestParts (pGomega nO) : Blk').place = _
  rw [place_of_k12]
  exact place_of_p12At _ _

theorem sharedEnd_place (Cl' : Type) (P : _root_.Desc.K14.P14) (N : H2U.Places4) :
    (sharedEnd Cl' P N).place = ⟨2, none, 11, .frame⟩ := rfl


theorem shared_places (Cl' : Type) (c : OnBytes.Model.Verify.Chains) (P : _root_.Desc.K14.P14)
    (N : H2U.Places4) :
    ((_root_.Desc.K14.chainOf c P (Seat.tests N) Seat.last).retype (Cl' := Cl')).blocksInOrder.map (·.place) =
      (sharedPre Cl' c P N).map (·.place) ++ ⟨2, none, 9, .K12⟩ ::
        ((if N.O.isSome then [⟨2, none, 10, .K12⟩] else []) ++ [⟨2, none, 11, .frame⟩]) := by
  rw [shared_cut]
  cases hO : N.O with
  | none => simp [guEntry_place, sharedEnd_place]
  | some nO => simp [guEntry_place, omegaEntry_place, sharedEnd_place]

/-! ## For the shared chain's files' rule on chainOf's places -/

/-- The two tests as the seat's text lays them, where the plan has a test on G_omega. -/
theorem tests_places (N : H2U.Places4) (nO : H2U.PlaceNums) (hO : N.O = some nO) :
    (Seat.tests N).map (·.place) = [⟨2, none, 9, .K12⟩, ⟨2, none, 10, .K12⟩] := by
  unfold Seat.tests
  rw [hO]
  show [(proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U) : Blk').place,
    (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) : Blk').place] = _
  rw [place_of_k12, place_of_k12, place_of_p12At, place_of_p12At]

/-- Where it has none: the test on G_u alone. -/
theorem tests_places_none (N : H2U.Places4) (hO : N.O = none) :
    (Seat.tests N).map (·.place) = [⟨2, none, 9, .K12⟩] := by
  unfold Seat.tests
  rw [hO]
  show [(proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ N.U) : Blk').place] = _
  rw [place_of_k12, place_of_p12At]

theorem last_place (front : List (Block _root_.Desc.K14.St Unit)) :
    (Seat.last front).place = ⟨2, none, 11, .frame⟩ := rfl

/-- The chain retyped has the chain's own places. -/
theorem retype_places (Cl' : Type) (c : OnBytes.Model.Verify.Chains) (P : _root_.Desc.K14.P14)
    (tests : List (Block _root_.Desc.K14.St Unit))
    (last : List (Block _root_.Desc.K14.St Unit) → Block _root_.Desc.K14.St Unit) :
    ((_root_.Desc.K14.chainOf c P tests last).retype (Cl' := Cl')).blocksInOrder.map (·.place) =
      (_root_.Desc.K14.chainOf c P tests last).blocksInOrder.map (·.place) := by
  rw [Chain.flat_eq, Chain.flat_eq]
  simp [Chain.retype, _root_.Desc.K14.chainOf, List.map_append, List.map_map, Function.comp_def,
    Block.asBare, Block.retype]

/-- A block whose retyped fellow passes the flat list's test on the plan passes it too. -/
theorem asBare_of_retype {S Cl : Type} (Cl' : Type) (b : Block S Cl)
    (h : ((b.retype (Cl' := Cl')).asBare).planOk = true) : b.asBare.planOk = true := by
  simp only [Block.asBare, Block.retype, Block.hasNoClaimsAndNothingAfter, Bool.and_eq_true] at h ⊢
  tauto

/-- Where every entry of the retyped chain's flat list passes its test on the plan, so does every
entry of the chain's own. -/
theorem retype_planOk (Cl' : Type) (c : OnBytes.Model.Verify.Chains) (P : _root_.Desc.K14.P14)
    (tests : List (Block _root_.Desc.K14.St Unit))
    (last : List (Block _root_.Desc.K14.St Unit) → Block _root_.Desc.K14.St Unit)
    (h : ∀ b ∈ ((_root_.Desc.K14.chainOf c P tests last).retype (Cl' := Cl')).blocksInOrder,
      b.planOk = true) :
    ∀ b ∈ (_root_.Desc.K14.chainOf c P tests last).blocksInOrder, b.planOk = true := by
  intro b hb
  rw [Chain.flat_eq] at hb h
  simp only [Chain.retype, _root_.Desc.K14.chainOf, List.map_nil, List.flatMap_nil,
    List.append_nil, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
    or_false] at hb h
  rcases hb with (rfl | ⟨x, hx, rfl⟩) | rfl
  · have h1 := h _ (.inl (.inl rfl))
    simp only [Block.asBare, Block.retype, Block.hasNoClaimsAndNothingAfter, Bool.and_eq_true] at h1 ⊢
    tauto
  · exact asBare_of_retype Cl' x (h _ (.inl (.inr ⟨x.retype, ⟨x, hx, rfl⟩, rfl⟩)))
  · exact asBare_of_retype Cl' _ (h _ (.inr rfl))

end H2K.JointK

#print axioms H2K.JointK.place_of_k12
#print axioms H2K.JointK.guEntry_place
#print axioms H2K.JointK.omegaEntry_place
#print axioms H2K.JointK.sharedEnd_place
#print axioms H2K.JointK.shared_places
#print axioms H2K.JointK.tests_places
#print axioms H2K.JointK.last_place
#print axioms H2K.JointK.retype_places
#print axioms H2K.JointK.retype_planOk
