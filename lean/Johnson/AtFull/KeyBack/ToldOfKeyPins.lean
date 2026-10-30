-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/ToldOfKeyPins.lean: `Key.toldOfMade m` RETURNS THE WRITTEN TABLE
`Johnson.KB4.toldKeyFull`, FROM THE PINS ALONE. One call: `toldOfMade_at_pins` (ToldAtPins.lean) at
the three closed facts on the labels' groups (`groups_keySends0`, `1`, `2`,
Johnson/AtFull/KeyBack/LabelsKey.lean).
Limits. `KeyPins m` (Pins.lean) IS SHOWN AT NO m HERE: eight equations of m's fields to the full
size's written values. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.ToldAtPins
import Johnson.AtFull.KeyBack.LabelsKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key

/-- **r1's table at the written value, from the pins alone.** -/
theorem toldOfMade_of_keyPins (m : Made) (h : KeyPins m) :
    toldOfMade m = .ok Johnson.KB4.toldKeyFull :=
  toldOfMade_at_pins m h groups_keySends0
    groups_keySends1 groups_keySends2

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.toldOfMade_of_keyPins
