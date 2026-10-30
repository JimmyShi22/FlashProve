-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT THE KEY FILE's TWO LOOKUPS: THE OFFLINE PROVER.
WHAT IT IS FOR: each lookup is laid at `lookOf` (E2E/KeyLookups.lean). The theorems on the lookups at the first thread ask its
  place, its face and its number of rounds in front (`base`) as premises, and `LookupStandsAtTheKeyBook` leaves `base` free. Here
  `lookOf` meets all of these.

E2E/Lookup/Key/LookupsOfTheNamedPartsStandAtTheirBorders.lean. Theorems with proofs.

  `baseAtIsTheRoundsInFrontOfTheBorder`   `baseAt` is `roundsTo` of the thread's list at border 4 or 10
  `lookOfStandsAtItsBorder`               place, face and base of `lookOf`
  `lookOfStandsAtTheKeyBook`              `LookupStandsAtTheKeyBook` at `lookOf`

Limits. Public data alone, in scope, at the written sizes. Nothing on any property of a protocol.
-/
import E2E.Lookup.Key.LookupValuesAtTheNamedParts
import E2E.Lookup.Key.LookupBehindAndRidesPastAtTheKey
import E2E.Lookup.Key.LookupSidePaysAtTheKeyBook
import E2E.KeyPlacesNamed
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SitePays

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.Lookup.Key
open ProofFile.Honest
open AtPublicFiles.KeyBook
open AtPublicFiles.KeyThread
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.KeyValues (baseAt lookAt lookOf placeAt)
open VerifiableInference.Desc.K3 (faceOfLkp)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi)
open ProofFile.Honest.K3.Parts.Key (faceK)
open Inst.Model.Layout (kRef)

section
variable {Bk : ProverCoinCounts} {W₀ Rc Cells M Smp Rec X' : Type} (source : Source) (numbers : H2U.PlaceNums)
  (later : LaterPlaces) (filling : KeyFill Bk W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  {halves : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X')}
  {tables : Fmt.TreeSource → Coins Bk → Local W₀ Rc Xi Unit → List Fmt.Drawn →
    VerifiableInference.Desc.Place × Table}
  {files : VerifierAndGoals.PublicFiles}

theorem placesOfTheWrittenChainStandOnce : (fullFirst.map (·.1)).Nodup := by decide

/-- **A lookup's rounds in front, as baseAt counts them, are the rounds in front of its border.** -/
theorem baseAtIsTheRoundsInFrontOfTheBorder (sourced : KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) (number : Nat) (below : number < 2) :
    baseAt source numbers number =
      roundsTo (laid₁ source numbers later filling w₀ rc x halves tables).bs
        (if number = 0 then 4 else 10) := by
  have hRows := (places_named scope sourced.named).1
  have hOnce : ((laid₁ source numbers later filling w₀ rc x halves tables).bs.map (·.place)).Nodup := by
    have hPlaces : (laid₁ source numbers later filling w₀ rc x halves tables).bs.map (·.place) =
        fullFirst.map (·.1) := by
      rw [← hRows]
      simp only [Johnson.RunOne.Sound.rowsOf, List.map_map]
      rfl
    rw [hPlaces]
    exact placesOfTheWrittenChainStandOnce
  obtain ⟨atFour, atTen, -⟩ := lookupBordersAreFourAndTen source numbers later filling w₀ rc x
    (halves := halves) (tables := tables) sourced scope
  have hSome : ∀ p, (startIn fullFirst p).isSome = true →
      ∃ n, roundsInFront (laid₁ source numbers later filling w₀ rc x halves tables).bs p = some n := by
    intro p hp
    obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 hp
    exact ⟨n, (start_named₁ scope sourced.named p).trans hn⟩
  have isLookup : number = 0 ∨ number = 1 := by omega
  rcases isLookup with rfl | rfl
  · obtain ⟨blk, hBlk, hPlace⟩ := Option.map_eq_some_iff.1 atFour
    obtain ⟨n, hn⟩ := hSome (lookPlace 0) (by decide)
    have hBorder := ProofFile.Honest.K3.Law.AtThr.borderNo_of_nodup _ 4 blk (lookPlace 0) hBlk hPlace hOnce
    have hRounds := roundsTo_inFront _ (lookPlace 0) n hn
    rw [hBorder] at hRounds
    show (roundsInFront (laid₁ source numbers later filling w₀ rc x halves tables).bs (lookPlace 0)).getD 0 =
      roundsTo _ 4
    rw [hn, hRounds]
    rfl
  · obtain ⟨blk, hBlk, hPlace⟩ := Option.map_eq_some_iff.1 atTen
    obtain ⟨n, hn⟩ := hSome (lookPlace 1) (by decide)
    have hBorder := ProofFile.Honest.K3.Law.AtThr.borderNo_of_nodup _ 10 blk (lookPlace 1) hBlk hPlace hOnce
    have hRounds := roundsTo_inFront _ (lookPlace 1) n hn
    rw [hBorder] at hRounds
    show (roundsInFront (laid₁ source numbers later filling w₀ rc x halves tables).bs (lookPlace 1)).getD 0 =
      roundsTo _ 10
    rw [hn, hRounds]
    rfl

/-- **Place, face and base of `lookOf`**: the three premises of the theorems on a lookup at the first thread. -/
theorem lookOfStandsAtItsBorder (sourced : KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) (number : Nat) (below : number < 2) :
    (lookOf source numbers number).place = lookPlace number ∧
      (lookOf source numbers number).face = faceOfLkp (lookAt source number) ∧
      (lookOf source numbers number).face = faceK 1 ⟨kRef, 3076096⟩ (writtenStructure number) ∧
      (lookOf source numbers number).base =
        roundsTo (laid₁ source numbers later filling w₀ rc x halves tables).bs
          (if number = 0 then 4 else 10) := by
  refine ⟨rfl, rfl, ?_, baseAtIsTheRoundsInFrontOfTheBorder source numbers later filling w₀ rc x
    sourced scope number below⟩
  show faceOfLkp (lookAt source number) = _
  rw [lookAtIsTheWrittenLookup sourced scope number below]
  rfl

end

/-- **`lookOf` stands at the key file's book.** -/
theorem lookOfStandsAtTheKeyBook {source : Source} {numbers : H2U.PlaceNums} {later : LaterPlaces}
    {files : VerifierAndGoals.PublicFiles} (sourced : KeySourced files source numbers later)
    (scope : VerifierAndGoals.InScope files = true) {data : KeyPub} (written : fullPub = some data)
    (number : Nat) (below : number < 2) :
    LookupStandsAtTheKeyBook data number (lookOf source numbers number) := by
  have hFaces := keyBookFacesAreTheWrittenFaces written
  have hFace : (lookOf source numbers number).face = faceK 1 ⟨kRef, 3076096⟩ (writtenStructure number) := by
    show faceOfLkp (lookAt source number) = _
    rw [lookAtIsTheWrittenLookup sourced scope number below]
    rfl
  have isLookup : number = 0 ∨ number = 1 := by omega
  refine ⟨rfl, ?_, by rw [hFaces]; rfl, ?_⟩
  · rw [hFace, hFaces]
    rcases isLookup with rfl | rfl <;> rfl
  · rw [hFace]
    obtain ⟨first, second, -⟩ := planesAtTheWrittenLookups
    rcases isLookup with rfl | rfl
    · show 2 ≤ (faceK 1 ⟨kRef, 3076096⟩ Johnson.Pack.lk0Full).planes
      omega
    · show 2 ≤ (faceK 1 ⟨kRef, 3076096⟩ Johnson.Pack.lk1Full).planes
      omega

end AtPublicFiles.Lookup.Key

#print axioms AtPublicFiles.Lookup.Key.placesOfTheWrittenChainStandOnce
#print axioms AtPublicFiles.Lookup.Key.baseAtIsTheRoundsInFrontOfTheBorder
#print axioms AtPublicFiles.Lookup.Key.lookOfStandsAtItsBorder
#print axioms AtPublicFiles.Lookup.Key.lookOfStandsAtTheKeyBook
