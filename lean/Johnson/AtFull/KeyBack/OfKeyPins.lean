-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/OfKeyPins.lean: r2 AND r3 OF THE KEY FILE's BACK AT THE WRITTEN VALUES, FROM
THE PINS ALONE. Calls alone: OfPins.lean and the four closed facts on the trees (FirstAFact,
FoldedBFact, OmegaBFact, OwnABFact).
  `rangesNumbers_of_keyPins`: `KeyPins m` gives `Key.rangesNumbers m = .ok
    Johnson.KB8.rangesNumsFull`.
  `laterPlaces_of_keyPins`: `KeyPins m` gives `Key.laterPlaces m = .ok Johnson.KB8.laterPlacesFull`.
Limits. `KeyPins m` (Pins.lean) IS SHOWN AT NO m: eight equations of m's fields to the full size's
written values. Until it is shown at the m that the key file's road makes, the two rows are not
paid. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.OfPins
import Johnson.AtFull.KeyBack.FirstAFact
import Johnson.AtFull.KeyBack.FoldedBFact
import Johnson.AtFull.KeyBack.OmegaBFact
import Johnson.AtFull.KeyBack.OwnABFact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key

/-- **r2 at the written value, from the pins alone.** -/
theorem rangesNumbers_of_keyPins (m : Made) (h : KeyPins m) :
    rangesNumbers m = .ok Johnson.KB8.rangesNumsFull :=
  rangesNumbers_of_pins m h first_A

/-- **r3 at the written value, from the pins alone.** -/
theorem laterPlaces_of_keyPins (m : Made) (h : KeyPins m) :
    laterPlaces m = .ok Johnson.KB8.laterPlacesFull :=
  laterPlaces_of_pins m h folded_B omega_B own_AB

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.rangesNumbers_of_keyPins
#print axioms Johnson.AtFull.KeyBack.laterPlaces_of_keyPins
