-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/KindsWithoutPlace.lean: THE KINDS OF SUB-PROTOCOL THAT HAVE NO PLACE ON THE
FIRST CHAIN: their share of the first chain's chain of promises is free.

Why. `KindTiedR N Mg links ps Rch E l K` (Johnson/Desc/Sound/TiedR.lean) asks a tie at every number
i at which the list of places ps has a place of the kind K. At a kind without a place in ps it asks
nothing. A top that has one field for each of the sixteen kinds therefore has fields that say
nothing. Here these are found by Lean's kernel and paid, so that a top can drop them.

Main names (namespace `VerifierAndGoals.AtTheName`).
  `kindTiedR_of_no_place`: no place of ps has the kind K → `KindTiedR … ps … K`. General.
  `noPlaceB ps K`: the test with code; `noPlace_of_B`: what its accept says;
    `kindTiedR_of_noPlaceB`.
  `sixteenKinds`: the sixteen values of `KindName`, in their order; `sixteenKinds_all`: none is
    left out.
  `placesOfKind ps K`: how many places of ps have the kind K.
  THE TABLE, BY THE KERNEL, at the first chain's written list at the full size,
  `flatPlacesOf P5J.fullLinks true` (358 places: `firstPlaces_358`):
    **`kindCount_full`**: K1 52 · K2 25 · K3 50 · K4 12 · K5 12 · K6 1 · K7 1 · K8 25 · K9 75 ·
      K10 25 · K11 1 · K12 1 · K13 1 · K14 0 · K15 0 · frame 77. (They add up to 358.)
    **`noPlace_full`**: the test accepts at K14 and K15 and rejects at the fourteen others.
    `noPlaceB_K12`: a negative line by itself: it rejects at K12.
  **`kind_free_K14`**, **`kind_free_K15`**: `KindTiedR` at that list of places and these two kinds:
    at all numbers N, meanings Mg, links, conditions Rch, extractors E and pieces l.

Limits. IT PAYS NO LAW: the two fields were empty. K14's and K15's laws are not on the first chain;
where they are owed (the shared chain, the copy's file) nothing here speaks. Of the fourteen kinds
with a place nothing is said. The full size alone, at "several" := true.
No soundness is claimed in this file.

-/
import Johnson.Desc.Sound.TiedR
import Johnson.P5J.MeansQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifierAndGoals.AtTheName

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (KindName Place)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start flatPlacesOf)

/-- The test with code: no place of the list has the kind K. -/
def noPlaceB (ps : List Place) (K : KindName) : Bool := ps.all fun a => a.kind != K

/-- What its accept says. -/
theorem noPlace_of_B {ps : List Place} {K : KindName} (h : noPlaceB ps K = true) (i : ℕ)
    (a : Place) (ha : ps[i]? = some a) : a.kind ≠ K := by
  have hm : a ∈ ps := List.mem_of_getElem? ha
  have h1 := List.all_eq_true.1 h a hm
  exact bne_iff_ne.1 h1

/-- How many places of the list have the kind K. -/
def placesOfKind (ps : List Place) (K : KindName) : ℕ := (ps.filter fun a => a.kind == K).length

/-- The sixteen kinds, in their order. -/
def sixteenKinds : List KindName :=
  [.K1, .K2, .K3, .K4, .K5, .K6, .K7, .K8, .K9, .K10, .K11, .K12, .K13, .K14, .K15, .frame]

/-- None is left out. -/
theorem sixteenKinds_all (K : KindName) : K ∈ sixteenKinds := by
  cases K <;> decide

/-- The first chain's written list at the full size has 358 places. -/
theorem firstPlaces_358 : (flatPlacesOf P5J.fullLinks true).length = 358 := by decide +kernel

/-- **THE TABLE: how many places each kind has on the first chain.** By the kernel. -/
theorem kindCount_full : sixteenKinds.map (placesOfKind (flatPlacesOf P5J.fullLinks true)) =
    [52, 25, 50, 12, 12, 1, 1, 25, 75, 25, 1, 1, 1, 0, 0, 77] := by decide +kernel

/-- **The test at each of the sixteen**: it accepts at K14 and K15 alone. By the kernel. -/
theorem noPlace_full : sixteenKinds.map (noPlaceB (flatPlacesOf P5J.fullLinks true)) =
    [false, false, false, false, false, false, false, false, false, false, false, false, false,
      true, true, false] := by decide +kernel

theorem noPlaceB_K14 : noPlaceB (flatPlacesOf P5J.fullLinks true) .K14 = true := by decide +kernel

theorem noPlaceB_K15 : noPlaceB (flatPlacesOf P5J.fullLinks true) .K15 = true := by decide +kernel

/-- A negative line: the test can reject. -/
theorem noPlaceB_K12 : noPlaceB (flatPlacesOf P5J.fullLinks true) .K12 = false := by decide +kernel

section
variable {Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
  (links : List ModelPart) (ps : List Place)
  (Rch : ℕ → (P × VerifiableInference.Desc.First.S) × Fr.E.Str → Prop)
  (E : ℕ → (P × VerifiableInference.Desc.First.S) × Fr.E.Str →
    (P × VerifiableInference.Desc.First.S) × Fr.E.Str → W → W)
  (l : List (Piece C Fr (P × VerifiableInference.Desc.First.S) Cl W))

/-- **At a kind without a place the share is free.** -/
theorem kindTiedR_of_no_place (K : KindName)
    (h : ∀ (i : ℕ) (a : Place), ps[i]? = some a → a.kind ≠ K) :
    KindTiedR N Mg links ps Rch E l K :=
  fun i _ a _ ha hk => absurd hk (h i a ha)

/-- The same from the test's accept. -/
theorem kindTiedR_of_noPlaceB (K : KindName) (h : noPlaceB ps K = true) :
    KindTiedR N Mg links ps Rch E l K :=
  kindTiedR_of_no_place N Mg links ps Rch E l K (noPlace_of_B h)

/-- **K14's share of the first chain's chain of promises is free.** -/
theorem kind_free_K14 :
    KindTiedR N Mg links (flatPlacesOf P5J.fullLinks true) Rch E l KindName.K14 :=
  kindTiedR_of_noPlaceB N Mg links _ Rch E l _ noPlaceB_K14

/-- **K15's share of the first chain's chain of promises is free.** -/
theorem kind_free_K15 :
    KindTiedR N Mg links (flatPlacesOf P5J.fullLinks true) Rch E l KindName.K15 :=
  kindTiedR_of_noPlaceB N Mg links _ Rch E l _ noPlaceB_K15

end

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.noPlace_of_B
#print axioms VerifierAndGoals.AtTheName.sixteenKinds_all
#print axioms VerifierAndGoals.AtTheName.firstPlaces_358
#print axioms VerifierAndGoals.AtTheName.kindCount_full
#print axioms VerifierAndGoals.AtTheName.noPlace_full
#print axioms VerifierAndGoals.AtTheName.noPlaceB_K14
#print axioms VerifierAndGoals.AtTheName.noPlaceB_K15
#print axioms VerifierAndGoals.AtTheName.noPlaceB_K12
#print axioms VerifierAndGoals.AtTheName.kindTiedR_of_no_place
#print axioms VerifierAndGoals.AtTheName.kindTiedR_of_noPlaceB
#print axioms VerifierAndGoals.AtTheName.kind_free_K14
#print axioms VerifierAndGoals.AtTheName.kind_free_K15
