-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/WrittenList.lean: A LIGHT FILE: THE WRITTEN ROW OF SORTS AND THE WRITTEN LIST OF PLACES
OF THE PROOF FILE's FIRST CHAIN AT THE GOALS' 25 LINKS: CLOSED TERMS, so that every test on the
table can stand at ONE name.
IT IMPORTS THE DRIVER's Johnson/Desc/First/Driver/PlacesLaw.lean ALONE, AND NOTHING OF THIS FOLDER's SEATS.

  subW l            the sort of link number l: the head's at 24, else layers at an even, attention
                    at an odd number. (Johnson/IMR/LinkSeat.lean's subAt, letter for letter; that
                    file is heavy.)
  linksW · placesW  (List.range 25).map subW · flatPlacesOf linksW true.
  nAt l             the number of a link's blocks in front of its batching: 9 at l = 24, else 7.
  places_len        358 places: by the kernel.

That placesW is a description's list of places: Johnson/IMR/PlacesScope.lean's places_scope, in the
goals' scope. No soundness.
-/
import Johnson.Desc.First.Driver.PlacesLaw

set_option autoImplicit false

namespace IM

open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (ModelPart flatPlacesOf)

/-- The sort of link number l. -/
def subW (l : Nat) : ModelPart := if l = 24 then .head else if l % 2 = 0 then .layers else .attention

/-- The written row of sorts. -/
def linksW : List ModelPart := (List.range 25).map subW

/-- The written list of places. -/
def placesW : List Place := flatPlacesOf linksW true

/-- The number of a link's blocks in front of its batching. -/
def nAt (l : Nat) : Nat := if l = 24 then 9 else 7

set_option maxRecDepth 1000000 in
theorem places_len : placesW.length = 358 := by decide +kernel

end IM

#print axioms IM.places_len
