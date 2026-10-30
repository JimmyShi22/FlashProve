-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/PinIFront.lean: CLOSED FACTS. One test with code, its law, and two decisions by
Lean's kernel.

What is here. IN FRONT OF THE SUB-PROTOCOL OF THE FEED-FORWARD LAYERS' OWN ROUNDS (K4), AT EACH OF
ITS TWELVE PLACES OF THE WRITTEN LIST OF SEGMENTS, THE TABLE's ITEM pinI (the index masks' message
is pinned) IS OPEN. The library decides the like BEHIND the sub-protocol (`k4_pinI_full`,
Johnson/Road/K4/Rec/OpenNextAt.lean); the honest side's thread stands in front of its member, so it
wants the border in front. Where pinI is open the table's promise asks the public item indexIs (the
library's `indexIs_held`, the same file).

  `k4PinIFront`   the test: pinI is open at border k, at every place of K4's.
  `pinI_front_of_fit`   what an accept gives at a place of K4's.
  `k4_pinI_front_full`   **BY THE KERNEL**: it accepts at the written list; the places are twelve.
  `pinI_shut_at_two`   A NEGATIVE TEST THAT COULD FAIL: at border 2 pinI is not open.

Not shown here. THE LIST OF SEGMENTS IS WRITTEN (`linksFull`), not read off the public parameters.
Two closed facts by evaluation in Lean's kernel, which no independent checker has replayed. Nothing
on any state, script or prover. A program's walk from import to import, which reads import lines
alone and stops unopened at Johnson/Goal/, ThirdParty/, Johnson/D/, Johnson/Bridge/ and Cb/Bridge*,
stopped at 2 modules under Johnson/Goal/: so these counts are lower bounds; it met no module under
ThirdParty/, Johnson/D/ or Johnson/Bridge/ and none that begins Cb.Bridge.

No property is claimed.
-/
import Johnson.Road.K4.Rec.OpenNextAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open OnBytes.Road.K4.Riders (atK4s atK4s_at)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (ModelPart Item start openSets flatPlacesOf)
open VerifiableInference.Desc.First.FillK4 (isK4At)
open VerifiableInference.Desc.Sound (linksFull)

/-- pinI is open in front of K4's sub-protocol, at every place of K4's. A test with code. -/
def k4PinIFront (links : List ModelPart) (ps : List Place) : Bool :=
  atK4s links ps fun k _ => decide (Item.pinI ∈ (openSets links ps (start links))[k]?.getD [])

/-- What an accept gives at a place of K4's. CONDITIONAL on H and h. -/
theorem pinI_front_of_fit {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}
    (H : AtK4 links ps k m pl) (h : k4PinIFront links ps = true) :
    Item.pinI ∈ (openSets links ps (start links))[k]?.getD [] :=
  of_decide_eq_true (atK4s_at H h)

set_option maxRecDepth 1000000 in
/-- **BY THE KERNEL**: the test accepts at the written list, and the places are twelve. -/
theorem k4_pinI_front_full :
    (k4PinIFront linksFull (flatPlacesOf linksFull true) &&
      ((flatPlacesOf linksFull true).countP (isK4At linksFull) == 12)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test that could fail**: at border 2 pinI is not open. -/
theorem pinI_shut_at_two :
    decide (Item.pinI ∈
      (openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[2]?.getD []) =
      false := by
  decide +kernel

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.pinI_front_of_fit
#print axioms OnBytes.Road.K4.W.k4_pinI_front_full
#print axioms OnBytes.Road.K4.W.pinI_shut_at_two
