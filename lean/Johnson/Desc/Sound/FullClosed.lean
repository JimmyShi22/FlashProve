-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FullClosed.lean: "WHAT THE STORED TABLE DECODES TO": AT THE FULL SIZE's WRITTEN NUMBERS THE LIBRARY's DATA OF A DECODER WITH A RECORD, AS THE TOP STATEMENTS' CONFIGURATION HAS THEM (frS.toDecR frZ 402653181, OnBytes/Slice/FullRecLink.lean), ARE decROfS (Johnson/Desc/Sound/StoredAlong.lean) OF A SHAPE WHOSE TABLE HAS THE
CODE ⟨32, 402653184, 44040191⟩, 2^11 ROWS AND ONE ANSWER, AT THE RADIUS 2852142980. One definition, three theorems.

  decRIx: decROfS reads of a shape its table's shape alone · decROf_index: rfl.
  full_closed: the equation of closed terms, for every number of a salt's bytes (no field of the decoder's data reads it).
  full_of_index: so at every shape whose table's shape is that one.
WHAT IT IS NOT: that the release's plan HAS that table's shape: a premise here (a public fact on the plan). HOW THE EQUATION IS SPENT where types hang on the data (the claims, the rest, the records): along the equation, by whoever lays it in: NOT DONE HERE.

Limits. The full size alone. NO MEMBER.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.StoredAlong
import OnBytes.Slice.FullRecLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain

/-- The library's data of a decoder with a record, off a table's shape. -/
@[reducible] def decRIx (ix : IndexShape) (eM : Nat) : DecR :=
  { T := codeOf ix.code, v := ix.v, eM := eM, Z := recZ ix.code.ell ix.cubeBits ix.answers, cut := ix.plain }

/-- decROfS reads the table's shape alone. -/
theorem decROf_index (S : FoldeqShape) (eM : Nat) : decROfS S eM = decRIx S.index eM := rfl

/-- **The equation of closed terms at the full size.** -/
theorem full_closed (sb : Nat) :
    decRIx ⟨⟨32, 402653184, 44040191⟩, 11, 1, sb⟩ 2852142980 = frS.toDecR frZ 402653181 := by
  have h29 : ceilLog2 402653184 = 29 := by decide +kernel
  unfold decRIx IndexShape.cubeBits Code.logEll
  simp only [h29]
  rfl

/-- So at every shape whose table's shape is that one. -/
theorem full_of_index (S : FoldeqShape) (sb : Nat)
    (h : S.index = ⟨⟨32, 402653184, 44040191⟩, 11, 1, sb⟩) :
    decROfS S 2852142980 = frS.toDecR frZ 402653181 := by
  rw [decROf_index, h]
  exact full_closed sb

end Desc.K14.Law

#print axioms Desc.K14.Law.decROf_index
#print axioms Desc.K14.Law.full_closed
#print axioms Desc.K14.Law.full_of_index
