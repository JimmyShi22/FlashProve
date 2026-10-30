-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRunsSharedSixFields.lean: the six fields of `KeyOthersPlay` (E2E/OfflineRunsKey.lean) at the shared chain's
places that are no test, from `blockPlays_six_atAll` (E2E/OfflineRunsSharedSixAtKey.lean), which speaks by a
member's number: which number bears which place.

  `shared_place_at`      in scope the member number j of the key file's shared list stands at the j-th of the twelve
                         written places
  `shared_number_of`     so a member at one of the six places has that place's number: 1, 2, 4, 5, 7, 8
  `shared_six_fields`    the six fields, at every book, every input, and letters K that bear the sixteen places
                         and whose two sendings are made at the key's parameters

Calls and a count by evaluation. Nothing on any property.
-/
import E2E.OfflineRunsSharedSixAtKey
import E2E.OfflineRunsKey
import E2E.KeyPlacesNamed
import E2E.OfflineSides

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open OnBytes (TableKey)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeyBook (fullShared pointPlace foldedPlace locPlace omegaPlace zetaPlace splitPlace)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open VerifierAndGoals (PublicFiles InScope)

variable {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- In scope a member of the shared list stands at the written place of its number. -/
theorem shared_place_at (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {j : Nat}
    {b : Block (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl}
    (hb : (keyFileDescription Xs N Pl).shared.blocksInOrder[j]? = some b) :
    (fullShared.map (·.1))[j]? = some b.place := by
  obtain ⟨-, r2, -⟩ := AtPublicFiles.KeyBook.places_named scope hs.named
  rw [← places_of_rows r2, List.getElem?_map, hb]
  rfl

/-- Which number bears which of the six places: by evaluation over the twelve. -/
theorem shared_number_of {j : Nat} {p : Place} (h : (fullShared.map (·.1))[j]? = some p) :
    (p = pointPlace → j = 1) ∧ (p = foldedPlace → j = 2) ∧ (p = locPlace → j = 4) ∧
      (p = omegaPlace → j = 5) ∧ (p = zetaPlace → j = 7) ∧ (p = splitPlace → j = 8) := by
  have hlt : j < 12 := by
    by_contra hge
    have hn : (fullShared.map (·.1))[j]? = none :=
      List.getElem?_eq_none (by
        have : (fullShared.map (·.1)).length = 12 := by decide
        omega)
    rw [hn] at h
    cases h
  have key : ∀ i < 12, ∀ q ∈ fullShared.map (·.1), (fullShared.map (·.1))[i]? = some q →
      (q = pointPlace → i = 1) ∧ (q = foldedPlace → i = 2) ∧ (q = locPlace → i = 4) ∧
        (q = omegaPlace → i = 5) ∧ (q = zetaPlace → i = 7) ∧ (q = splitPlace → i = 8) := by
    decide
  exact key j hlt p (List.mem_of_getElem? h) h

variable {W₀ Rc X₀ X Wk : Type}

/-- **The six fields.** -/
theorem shared_six_fields (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) (Bk : ProverCoinCounts)
    (K : KeyParts W₀ Rc X₀ X Wk) (hK : K.AtAll) (hP : K.send.P = parKey Xs Pl)
    (common : Common W₀ Rc TableKey) :
    PlaysAtShared (keyFileDescription Xs N Pl) Bk (keyProver K) common pointPlace ∧
      PlaysAtShared (keyFileDescription Xs N Pl) Bk (keyProver K) common foldedPlace ∧
      PlaysAtShared (keyFileDescription Xs N Pl) Bk (keyProver K) common locPlace ∧
      PlaysAtShared (keyFileDescription Xs N Pl) Bk (keyProver K) common omegaPlace ∧
      PlaysAtShared (keyFileDescription Xs N Pl) Bk (keyProver K) common zetaPlace ∧
      PlaysAtShared (keyFileDescription Xs N Pl) Bk (keyProver K) common splitPlace := by
  have six := blockPlays_six_atAll (Bk := Bk) hs scope K hK hP
    fun j => MidForm startNone (roundsIn (keyFileDescription Xs N Pl).shared.blocksInOrder j) common
  refine ⟨fun j b hb hp => ?_, fun j b hb hp => ?_, fun j b hb hp => ?_, fun j b hb hp => ?_,
    fun j b hb hp => ?_, fun j b hb hp => ?_⟩
  · exact six j (Or.inl ((shared_number_of (shared_place_at hs scope hb)).1 hp)) b hb
  · exact six j (Or.inr (Or.inl ((shared_number_of (shared_place_at hs scope hb)).2.1 hp))) b hb
  · exact six j (Or.inr (Or.inr (Or.inl
      ((shared_number_of (shared_place_at hs scope hb)).2.2.1 hp)))) b hb
  · exact six j (Or.inr (Or.inr (Or.inr (Or.inl
      ((shared_number_of (shared_place_at hs scope hb)).2.2.2.1 hp))))) b hb
  · exact six j (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ((shared_number_of (shared_place_at hs scope hb)).2.2.2.2.1 hp)))))) b hb
  · exact six j (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ((shared_number_of (shared_place_at hs scope hb)).2.2.2.2.2 hp)))))) b hb

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.shared_place_at
#print axioms AtPublicFiles.OfflineRows.shared_number_of
#print axioms AtPublicFiles.OfflineRows.shared_six_fields
