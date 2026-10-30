-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3ShapeBehind.lean: THE BOOK-KEEPING's FIRST Bool (shapeAt,
Johnson/Desc/First/Borders.lean) RIDES PAST A BLOCK WHOSE YES LEAVES ALL BUT THE OPEN LINK's OWN
PART (SameBut, Johnson/Desc/First/Look/K3CallsTurns.lean): a call of the rule
shapeAt_rides (Johnson/Desc/First/ShapeRides.lean), whose three facts on the two records SameBut
pays. General in the block: for both lookups. Statements and proofs; the rule's test on the table
(sameStand) evaluated at both lookups' places of the two written lists of segments. Ties: no error
term. NO SOUNDNESS IS CLAIMED.

OBJECT: no text that runs: the table's Bool shapeAt at two neighbouring borders.
USER: sameBut_shapeAt: Johnson/Desc/First/Look/K3CallsBehind.lean, K3CallsBehindR.lean ·
  sameBut_standOf: K3DigitsBehind.lean.
LETTERS: s, s' with SameBut s s'; links; p, p': the places of the block and of the next one.

Main names:
  `sameBut_standOf`: SameBut leaves where the state stands.
  `sameBut_shapeAt`: shapeAt at p in front, SameBut, sameStand links p p': shapeAt at p' behind.
  `standAtB links m pc`: sameStand at the index's own neighbours, at the address (1, m, pc, K3).
  `stand_small`, `stand_full`: yes at both lookups of every segment, the head's too, at both lists;
    `stand_control`: no across a segment's end.

Limits. That a real description's index is the written one: not here.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.ShapeRides
import Johnson.Desc.First.Look.K3CallsTurns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open VerifiableInference.Desc
open VerifiableInference.Desc.First (ModelPart standOf shapeAt sameStand shapeAt_rides flatPlaces borderAt
  shift)

/-- SameBut leaves where the state stands. -/
theorem sameBut_standOf {s s' : Desc.First.S} (h : SameBut s s') : standOf s' = standOf s := by
  rcases h.sort with ⟨a, a', e, e'⟩ | ⟨a, a', e, e'⟩ | ⟨a, a', e, e', ho, ho'⟩
  · simp [standOf, e, e']
  · simp [standOf, e, e']
  · simp [standOf, Desc.First.S.inLink, Desc.First.S.fork?, e, e', ho, ho']

/-- **shapeAt rides.** -/
theorem sameBut_shapeAt {s s' : Desc.First.S} (h : SameBut s s') {links : List ModelPart} {p p' : Place}
    (hf : sameStand links p p' = true) (h0 : shapeAt links (some p) s = true) :
    shapeAt links (some p') s' = true :=
  shapeAt_rides links p p' s s' hf (sameBut_standOf h)
    (by
      unfold Desc.First.S.noneWaits
      rw [h.rowsOwed])
    (by rw [h.link]) h0

/-- The test at the index's own neighbours. -/
def standAtB (links : List ModelPart) (m pc : ℕ) : Bool :=
  ((borderAt (flatPlaces true links true) ⟨1, some m, pc, .K3⟩).bind fun k =>
    ((flatPlaces true links true)[k + 1]?).map fun p' =>
      sameStand links ⟨1, some m, pc, .K3⟩ p').getD false

/-- Both lookups of all segments of a list. -/
def standAllB (links : List ModelPart) : Bool :=
  links.zipIdx.all fun x =>
    standAtB links x.2 (2 + shift x.1) && standAtB links x.2 (7 + shift x.1)

/-- The two written lists. -/
def shapeSmall : List ModelPart := [.layers, .attention, .layers, .attention, .head]
def shapeFull : List ModelPart :=
  (List.range 24).map (fun i => if i % 2 == 0 then ModelPart.layers else ModelPart.attention) ++ [.head]

theorem stand_small : standAllB shapeSmall = true := by decide +kernel

theorem stand_full : standAllB shapeFull = true := by decide +kernel

/-- A control: across a segment's end the test says no: the last place of segment 0 against the
first of segment 1. -/
theorem stand_control :
    (((flatPlaces true shapeSmall true).zip ((flatPlaces true shapeSmall true).drop 1)).filter
      fun x => x.1.link == some 0 && x.2.link == some 1).all
      (fun x => !sameStand shapeSmall x.1 x.2) = true ∧
    (((flatPlaces true shapeSmall true).zip ((flatPlaces true shapeSmall true).drop 1)).filter
      fun x => x.1.link == some 0 && x.2.link == some 1).length = 1 := by decide +kernel

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.sameBut_standOf
#print axioms VerifiableInference.OnPublicFiles.sameBut_shapeAt
#print axioms VerifiableInference.OnPublicFiles.stand_small
#print axioms VerifiableInference.OnPublicFiles.stand_full
#print axioms VerifiableInference.OnPublicFiles.stand_control
