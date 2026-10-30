-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.DescN
import Johnson.Desc.K12.Law.SharedPlaces
import Johnson.Desc.K12.Law.RoundsMore
import Johnson.Desc.K14.Law.PlacesAtChain
/-
Johnson/Loose/H2K12/SharedPlacesAtDescN.lean: (L1) AT descN, WITHOUT THE SCOPE AND WITHOUT proofDataAndDecisionOfPublicFiles: THE
HALF OF H2K12/SharedPlacesAtSeat.lean THAT NEEDS descN AND THE SHARED CHAIN's CUT ALONE,
so that it can stand over the library's own texts
before the first chain's half does. FACTS ON THE
PLAN. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  descN_places₂     the shared chain's flat list's places = ‹the nine in front, a letter› ++
      ⟨2, none, 9, .K12⟩ :: ((if N.O.isSome then [⟨2, none, 10, .K12⟩] else []) ++ [⟨2, none, 11, .frame⟩])
  split_at_seat | noSplit_at_seat   one call of our H2K.Pub.places_split (K12/Law/RoundsMore.lean)
  l1_at_seat        (descN o mk guardedProximityTestParts Z N c).planOk = true · N.O = some nO ⇒ placesFitS
      (descN …).shared (sharedPlaces true) = true: over places_at_chainOf |
      places_at_retype (Johnson/Desc/K14/Law/PlacesAtChain.lean)
  l1_not_one        A CONTROL: … (sharedPlaces false) = false
  sharedPre_length  (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).length = 9
IN THE SCOPE AND AT proofDataAndDecisionOfPublicFiles's RETURN: H2K12/SharedPlacesAtSeat.lean, over this file.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's
end.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12


theorem descN_places₂ (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (X : Parts T12) (Z : ProofFile.Pub)
    (N : H2U.Places4) (c : Chain First.S ProofFile.Cl) :
    (descN o mk X Z N c).shared.blocksInOrder.map (·.place) =
      (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).map (·.place) ++ ⟨2, none, 9, .K12⟩ ::
        ((if N.O.isSome then [⟨2, none, 10, .K12⟩] else []) ++ [⟨2, none, 11, .frame⟩]) :=
  shared_places ProofFile.Cl _ _ N

theorem split_at_seat (Z : ProofFile.Pub) (N : H2U.Places4) (hN : H2U.placesOfMade Z.made = .ok N)
    (nO : H2U.PlaceNums) (hO : N.O = some nO) :
    Z.made.p.chains.made.sized.proof.batch.shape.sharedSplitNeeded = true :=
  H2K.Pub.places_split Z.made N hN nO hO

/-- The same turned: where the shape does not split the places have no test on G_omega. -/
theorem noSplit_at_seat (Z : ProofFile.Pub) (N : H2U.Places4) (hN : H2U.placesOfMade Z.made = .ok N)
    (hs : Z.made.p.chains.made.sized.proof.batch.shape.sharedSplitNeeded = false) : N.O = none := by
  cases hO : N.O with
  | none => rfl
  | some nO => rw [split_at_seat Z N hN nO hO] at hs; cases hs

/-! ## (L1) -/

open VerifiableInference.Desc.Shared (placesFitS sharedPlaces)


theorem l1_at_seat (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (nO : H2U.PlaceNums) (hO : N.O = some nO) :
    placesFitS (descN o mk guardedProximityTestParts Z N c).shared (sharedPlaces true) = true := by
  obtain ⟨_, b2, _⟩ := Keeps.planOk_blocks _ hp
  have hpl := retype_planOk ProofFile.Cl Z.p.chains (p14N Z N) (Seat.tests N) Seat.last b2
  have h1 := (_root_.Desc.K14.Law.places_at_chainOf Z.p.chains (p14N Z N) (Seat.tests N) Seat.last
    hpl (tests_places N nO hO) (last_place _)).1
  have h2 := _root_.Desc.K14.Law.places_at_retype (Cl' := ProofFile.Cl) Z.p.chains (p14N Z N)
    (Seat.tests N) Seat.last hpl (tests_places N nO hO) (last_place _)
  rw [h1] at h2
  exact h2

/-- A CONTROL: the letter's other value fails there. -/
theorem l1_not_one (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (nO : H2U.PlaceNums) (hO : N.O = some nO) :
    placesFitS (descN o mk guardedProximityTestParts Z N c).shared (sharedPlaces false) = false := by
  have h := l1_at_seat o mk Z N c hp nO hO
  unfold placesFitS at h ⊢
  rw [beq_iff_eq] at h
  rw [h]
  decide

/-- WHAT STANDS IN FRONT OF THE TEST ON G_u IS NINE BLOCKS: so the two tests' numbers in the flat
list are 9 and 10. Off the two equations on the list's places, by their lengths. -/
theorem sharedPre_length (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (nO : H2U.PlaceNums) (hO : N.O = some nO) :
    (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).length = 9 := by
  have h := l1_at_seat o mk Z N c hp nO hO
  unfold placesFitS at h
  rw [beq_iff_eq, descN_places₂, hO] at h
  have hl := congrArg List.length h
  have h12 : (sharedPlaces true).length = 12 := by decide
  rw [h12, List.length_append, List.length_map] at hl
  have h3 : (({ chain := 2, link := none, piece := 9, kind := .K12 } : Place) ::
      ((if (some nO : Option H2U.PlaceNums).isSome then
          [({ chain := 2, link := none, piece := 10, kind := .K12 } : Place)] else []) ++
        [({ chain := 2, link := none, piece := 11, kind := .frame } : Place)])).length = 3 := rfl
  rw [h3] at hl
  omega

end H2K.JointK

#print axioms H2K.JointK.descN_places₂
#print axioms H2K.JointK.split_at_seat
#print axioms H2K.JointK.noSplit_at_seat
#print axioms H2K.JointK.l1_at_seat
#print axioms H2K.JointK.l1_not_one
#print axioms H2K.JointK.sharedPre_length
