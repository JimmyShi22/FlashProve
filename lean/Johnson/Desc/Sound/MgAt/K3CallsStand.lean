-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/MgAt/K3CallsStand.lean: THE LOOKUP ON A LINK's CALLS: THE FIELD stand OF THE
KIND's LEDGER (AttOwedR, LayOwedR: Johnson/Desc/Sound/MgAt/K3Owed.lean; AttRestR, LayRestR): "the
place of the lookup on the calls and the place behind it stand alike" (sameStand,
Johnson/Desc/First/ShapeRides.lean), AT ALL 25 SEGMENTS OF THE FULL SIZE's WRITTEN LIST, at the
terms of K3Pins.lean for the two places (MgAt.placeOf l false, MgAt.nextOf l false:
Johnson/Desc/Sound/MgAt/K3Pins.lean): one test by the kernel, with a negative test. It reads no
state of the verifier. NO SOUNDNESS IS CLAIMED.

OBJECT: the table of joints: no sub-protocol's text.
Used by K3CallsTests.lean (Johnson/Desc/Sound/MgAt/) · K03HeadPartsAt.lean, K03LeftAt.lean
  (Johnson/P5J/).
LETTERS: l: a segment below 25.

Main names: `standB` · `standB_full` (by the kernel) · `standB_wrong` (A NEGATIVE TEST: the place
  behind the lookup of ANOTHER segment does not stand alike) · `stand_at`.

Limits. The full size's written list alone. The calls' 25 places (not the digits').
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3Pins
import Johnson.Desc.First.ShapeRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Sound.MgAt (placeOf nextOf)
open VerifiableInference.Desc.First (sameStand)

/-- The place of the lookup on the calls and the place behind it stand alike, at all 25. -/
def standB : Bool :=
  (List.range 25).all fun l => sameStand linksFull (placeOf l false) (nextOf l false)

set_option maxRecDepth 1000000 in
theorem standB_full : standB = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the test can fail. -/
theorem standB_wrong : sameStand linksFull (placeOf 0 false) (nextOf 1 false) = false := by
  decide +kernel

/-- **stand, at a segment.** -/
theorem stand_at {l : ℕ} (hl : l < 25) :
    sameStand linksFull (placeOf l false) (nextOf l false) = true :=
  List.all_eq_true.1 standB_full l (List.mem_range.2 hl)

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.standB_full
#print axioms VerifiableInference.OnPublicFiles.standB_wrong
#print axioms VerifiableInference.OnPublicFiles.stand_at
