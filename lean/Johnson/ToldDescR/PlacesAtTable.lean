-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/PlacesAtTable.lean: no soundness is claimed.
The two later chains of every description that onlineDescription makes stand at the places of the two later chains' tables, said with the tables' own names (lastPlaces, Johnson/Desc/Last/BordersLast.lean · sharedPlaces | placesFitS, Johnson/Desc/Shared/BordersShared.lean): the last chain without a premise; the shared chain under the description's tests on the plan (F.planOk = true).
  fourPlaces_eq | sharedList_eq   this folder's written lists are the tables': rfl
  **last_fits_descPure**     placesFitS F.second lastPlaces = true · F.second.blocksInOrder.length = lastPlaces.length
  blocksOr_ok                where the shared chain's blocks pass their tests on the plan, so do the eight's stand-ins: so the eight can be said
  shared_ok_of_planOk        planOk's third clause
  **shared_fits_descPure**   under F.planOk = true: ∃ Z N, the road has made Z · placesOfMade Z.made = .ok N · placesFitS F.shared (sharedPlaces N.O.isSome) = true · F.shared.blocksInOrder.length = (sharedPlaces N.O.isSome).length
F.shared | F.second are the seats' chains carried by Chain.retype: the places and blocksOk come through places_retype | blocksOk_retype (Retype.lean); onlineDescription and its road take the letter o. The two tables' files (BordersLast.lean | BordersShared.lean) stand beneath this file.
Who reads each letter. ∃ Z N: the public part that the road has made of the three files, and the four tests' numbers off its plan: each stands with the equation that fixes it. split := N.O.isSome: «the plan has a second test on the shared chain».
Does not show. That the pieces' lists T.l₂ | T.l₃ of a rule are one shorter than the flat lists (the cutting's law). The first chain's length. That N.O.isSome is the shape's sharedSplitNeeded. Nothing on soundness.
-/
import Johnson.ToldDescR.SharedPlaces
import Johnson.Desc.Last.BordersLast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open ProofFile
open VerifiableInference.Desc (Block Chain FileDescription Place KindName blocksOk)
open VerifiableInference.Desc.Shared (sharedPlaces placesFitS)
open VerifiableInference.Desc.Last (lastPlaces)
open Desc.K14 (blocks blocksOr P14 St p14Of beforePointOf)

theorem fourPlaces_eq : fourPlaces = lastPlaces := rfl
theorem sharedList_eq (b : Bool) : sharedList b = sharedPlaces b := rfl

/-- **The last chain stands at its table's places.** -/
theorem last_fits_descPure {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : onlineDescription o pol lay KL = .ok F) :
    placesFitS F.second lastPlaces = true ∧ F.second.blocksInOrder.length = lastPlaces.length := by
  have e := last_places_descPure h
  rw [fourPlaces_eq] at e
  refine ⟨?_, ?_⟩
  · unfold placesFitS
    rw [e]
    exact beq_self_eq_true _
  · have k := congrArg List.length e
    rwa [List.length_map] at k

/-- Where the shared chain's blocks pass their tests on the plan, so do the blocks laid for the eight.
-/
theorem blocksOr_ok (c : OnBytes.Model.Verify.Chains) (P : P14) (ts : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit)
    (h : blocksOk (Desc.K14.chainOf c P ts last).blocksInOrder = true) :
    (blocksOr P).all (·.planOk) = true := by
  rw [List.all_eq_true]
  intro b hb
  have hm : ({ b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } : Block St Unit) ∈
      (Desc.K14.chainOf c P ts last).blocksInOrder := by
    unfold Desc.K14.chainOf Chain.blocksInOrder
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.2
      ⟨b, List.mem_append_left _ hb, rfl⟩))
  have k := List.all_eq_true.1 h _ hm
  simp only [Bool.and_eq_true] at k
  exact k.1.1

/-- The tests on the plan hold the shared chain's blocks' own. -/
theorem shared_ok_of_planOk {Xi : Type} (F : FileDescription Xi) (h : F.planOk = true) :
    blocksOk F.shared.blocksInOrder = true := by
  unfold FileDescription.planOk FileDescription.planOkCore at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1.1.1.1.1.2

/-- **The shared chain stands at its table's places**, under the tests on the plan. -/
theorem shared_fits_descPure {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (h : onlineDescription o pol lay KL = .ok F) (hp : F.planOk = true) :
    ∃ (Z : ProofFile.Pub) (N : H2U.Places4), pureRoad.pub o pol lay KL = .ok Z ∧
      H2U.placesOfMade Z.made = .ok N ∧
      placesFitS F.shared (sharedPlaces N.O.isSome) = true ∧
      F.shared.blocksInOrder.length = (sharedPlaces N.O.isSome).length := by
  have hs := shared_ok_of_planOk F hp
  obtain ⟨Z, hZ, h⟩ := ProofFile.Law.descPure_made h
  obtain ⟨A, B, c, hA, -, rfl⟩ := pureZ_make h
  have hA' : laterShared Z = some A := hA
  cases hN : H2U.placesOfMade Z.made with
  | error e =>
    unfold laterShared Desc.K14.sharedSeatAt at hA'
    rw [hN] at hA'
    exact nomatch hA'
  | ok N =>
    have hs' : blocksOk A.chain.blocksInOrder = true :=
      (blocksOk_retype (Cl' := ProofFile.Cl) A.chain (shared_links hA')).symm.trans hs
    have hA'' := hA'
    unfold laterShared Desc.K14.sharedSeatAt at hA''
    rw [hN] at hA''
    have e := Option.some.inj hA''
    have hc : blocksOk (Desc.K14.chainOf Z.p.chains (p14Of Z.p.chains (beforePointOf N))
        (VerifiableInference.Desc.K12.Seat.tests N)
        VerifiableInference.Desc.K12.Seat.last).blocksInOrder = true := by
      rw [← e] at hs'
      exact hs'
    obtain ⟨l, hl⟩ := eight_of_planOk (blocksOr_ok _ _ _ _ hc)
    have pl := (places_retype (Cl' := ProofFile.Cl) A.chain (shared_links hA')).trans
      (shared_places hA' hN hl)
    rw [sharedList_eq] at pl
    refine ⟨Z, N, hZ, hN, ?_, ?_⟩
    · show placesFitS (A.chain.retype : Chain A.σ ProofFile.Cl) _ = true
      unfold placesFitS
      rw [pl]
      exact beq_self_eq_true _
    · have k := congrArg List.length pl
      rwa [List.length_map] at k

end ToldDesc

#print axioms ToldDesc.last_fits_descPure
#print axioms ToldDesc.blocksOr_ok
#print axioms ToldDesc.shared_ok_of_planOk
#print axioms ToldDesc.shared_fits_descPure
