-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/EndFirstAt.lean: THE FIELD "END" OF `TablesFitR` (Johnson/P5J/TopTablesR.lean) AT
THE FULL SIZE's WRITTEN LIST: behind its last sub-protocol the first chain's table leaves open at
most `endFirst` (Johnson/Desc/Sound/TieEnd.lean): no mark, the pin on the committed table, the one
pending claim, the pins on the index and on W. A test on the table alone: no state, no key.

  `endB links ps k`: every member of the rule's list of open items at border k (`openL`,
    Johnson/Desc/Sound/SpineList.lean) is one of `endFirst`.
  `places_358`: the written list has 358 places. `end_yes`: `endB` says yes at border 358: both by
    `decide +kernel`.
  **`end_first_full`**: THE FIELD, to the letter, at links := `P5J.fullLinks` and
    ps := `flatPlacesOf fullLinks true`: by `openIsList`.
  NEGATIVE TESTS, = false, by the kernel: `end_no_mid`: at border 179 · `end_no_start`: at
    border 0. (`end_yes_before`: at border 357 it says yes already: the last place opens nothing.)

OBJECT: the table's rows. USER: Johnson/P5J/EndFieldFits.lean; meant: tables_fit's field END.
LETTERS: none.
Limits. It holds at the bytes of the table (Johnson/Desc/First/Borders.lean) over which it is
compiled. Nothing on soundness.
-/
import Johnson.Desc.Sound.TieEnd
import Johnson.Desc.Sound.SpineList
import Johnson.P5J.MeansQ

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.constructorNameAsVariable false

namespace VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item start flatPlacesOf)
open P5J (fullLinks)

/-- Every open item at border k is one of `endFirst`. -/
def endB (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  (openL (insL links ps) (outsL links ps) (start links) k).all fun i => endFirst.contains i

set_option maxRecDepth 1000000 in
theorem places_358 : (flatPlacesOf fullLinks true).length = 358 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem end_yes : endB fullLinks (flatPlacesOf fullLinks true) 358 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem end_yes_before : endB fullLinks (flatPlacesOf fullLinks true) 357 = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem end_no_mid : endB fullLinks (flatPlacesOf fullLinks true) 179 = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem end_no_start : endB fullLinks (flatPlacesOf fullLinks true) 0 = false := by decide +kernel

/-- **END, at the full size's written list.** -/
theorem end_first_full : ∀ i,
    openAfter (insQ fullLinks (flatPlacesOf fullLinks true))
      (outsQ fullLinks (flatPlacesOf fullLinks true)) (· ∈ start fullLinks)
      (flatPlacesOf fullLinks true).length i → i ∈ endFirst := by
  intro i h
  rw [places_358] at h
  have h2 : i ∈ openL (insL fullLinks (flatPlacesOf fullLinks true))
      (outsL fullLinks (flatPlacesOf fullLinks true)) (start fullLinks) 358 :=
    (openIsList Item _ _ _ 358 i).1 h
  have h3 := List.all_eq_true.1 end_yes i h2
  simpa using h3

end VerifiableInference.Desc.Sound

#eval (VerifiableInference.Desc.Sound.openL
  (VerifiableInference.Desc.Sound.insL P5J.fullLinks
    (VerifiableInference.Desc.First.flatPlacesOf P5J.fullLinks true))
  (VerifiableInference.Desc.Sound.outsL P5J.fullLinks
    (VerifiableInference.Desc.First.flatPlacesOf P5J.fullLinks true))
  (VerifiableInference.Desc.First.start P5J.fullLinks) 358).length

#print axioms VerifiableInference.Desc.Sound.places_358
#print axioms VerifiableInference.Desc.Sound.end_yes
#print axioms VerifiableInference.Desc.Sound.end_yes_before
#print axioms VerifiableInference.Desc.Sound.end_no_mid
#print axioms VerifiableInference.Desc.Sound.end_no_start
#print axioms VerifiableInference.Desc.Sound.end_first_full
