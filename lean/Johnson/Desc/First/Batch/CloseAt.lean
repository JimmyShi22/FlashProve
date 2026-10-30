-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/CloseAt.lean (kinds K9 and K10's joint place): A DEFINITION AND ONE
THEOREM: WHERE THE THREE BLOCKS THAT CLOSE A SEGMENT STAND, OFF K9's OWN NUMBERS.
A segment's closing is three blocks in a row (Johnson/Desc/First/Batch/Place.lean: closeOf p P): the
one equation (K9; no round) · the closing (K10; its rounds) · the segment is shut (K9; no round). A
maker of tables of places reads their places here and types no number of its own; IT OWES
`fits p P`: without that these are not closeOf's places:
  closePlaces p    the three places: pieces p.pieceEq, p.pieceEq + 1 and p.pieceEq + 2 of segment
                   p.link.
  closeOf_places   where the two kinds' numbers speak of one place (`fits p P`, which the first
                   block's test on the plan asks), these are closeOf's blocks' places.
FOR A HARNESS THAT HOLDS A RUN AGAINST `verify-on-bytes`'s STEPS: that verifier closes a segment in
ONE step ("8.call"; at the head "10.call"): its record stands behind the LAST of the three ("the
segment is shut"): so that step is answered for by the third block; behind the first and the second
there is no record of that verifier's to hold.

-/
import Johnson.Desc.First.Batch.Place

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par)

/-- The places of the three blocks that close segment p.link. -/
def closePlaces (p : Where) : List Place :=
  [⟨p.chain, some p.link, p.pieceEq, .K9⟩, ⟨p.chain, some p.link, p.pieceEq + 1, .K10⟩,
   ⟨p.chain, some p.link, p.pieceEq + 2, .K9⟩]

theorem closeOf_places {Cl : Type} (p : Where) (P : Par) (h : fits p P = true) :
    (closeOf (Cl := Cl) p P).map (·.place) = closePlaces p := by
  simp only [fits, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp [closeOf, closePlaces, closing, shut, oneEquation, Block.lift, First.Close.kind, h1, h2,
    ← h3]

end VerifiableInference.Desc.K9

#print axioms VerifiableInference.Desc.K9.closeOf_places
