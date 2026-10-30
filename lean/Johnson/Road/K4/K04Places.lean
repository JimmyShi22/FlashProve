-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K04Places.lean: IN THE DRIVER's WRITTEN LIST OF PLACES, AT THE FULL SIZE, THE KIND
K4 STANDS NOWHERE BUT AT THE TWELVE NUMBERS 28 g + 4. Two tests with code, a decision by the kernel,
one statement. In a file apart from K04Tied.lean, so that the row on where K4's block sits can
call it without the road to the table.

  `k4AtB`, `k4AllB`: the tests. `k4AllB_full`: the second says yes at `flatPlacesOf linksFull true`:
    `decide +kernel`.
  `k04_places_full`: an entry of that list of the kind K4 stands at a number 28 g + 4 with g < 12
    and is `k4PlaceAt g`.

Limits. It speaks of the WRITTEN list: `linksFull` is a definition of the table's writers' own
(Johnson/Desc/Sound/AtDriver.lean). That a description's own blocksInOrder list bears these places is not
said here. Nothing on soundness.
-/
import Johnson.Road.K4.K04Sits
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open VerifiableInference.Desc (KindName)
open VerifiableInference.Desc.First (flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)

/-- The test: number i and place a are those of K4's block in one of the twelve layers' segments. -/
def k4AtB (i : ℕ) (a : VerifiableInference.Desc.Place) : Bool :=
  (List.range 12).any fun g => i == 28 * g + 4 && decide (a = k4PlaceAt g)

/-- The test over a list of places: every entry of the kind K4 passes `k4AtB`. -/
def k4AllB (ps : List VerifiableInference.Desc.Place) : Bool :=
  (List.range ps.length).all fun i =>
    match ps[i]? with
    | some a => a.kind != KindName.K4 || k4AtB i a
    | none => true

set_option maxRecDepth 1000000 in
theorem k4AllB_full : k4AllB (flatPlacesOf linksFull true) = true := by decide +kernel

/-- **In the full list of places the kind K4 stands nowhere but at the twelve numbers 28 g + 4.**
That it stands at each of them is `atK4_full`'s. -/
theorem k04_places_full (i : ℕ) (a : VerifiableInference.Desc.Place)
    (ha : (flatPlacesOf linksFull true)[i]? = some a) (hk : a.kind = KindName.K4) :
    ∃ g, g < 12 ∧ i = 28 * g + 4 ∧ a = k4PlaceAt g := by
  have hi : i < (flatPlacesOf linksFull true).length := (List.getElem?_eq_some_iff.1 ha).1
  have h := List.all_eq_true.1 k4AllB_full i (List.mem_range.2 hi)
  rw [ha] at h
  have h2 : k4AtB i a = true := by
    rcases (Bool.or_eq_true _ _).mp h with h1 | h1
    · rw [hk] at h1
      exact absurd h1 (by decide)
    · exact h1
  obtain ⟨g, hg, h3⟩ := List.any_eq_true.1 h2
  obtain ⟨h5, h6⟩ := (Bool.and_eq_true _ _).mp h3
  exact ⟨g, List.mem_range.1 hg, by simpa using h5, of_decide_eq_true h6⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4AllB_full
#print axioms OnBytes.Road.K4.k04_places_full
