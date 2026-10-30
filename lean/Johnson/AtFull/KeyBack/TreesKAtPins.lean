-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/TreesKAtPins.lean: THE CORE `TreesK` FROM THE PINS ALONE. Calls and
rewritings.

`treesK_at_pins`: where m's sendings, plans and shape are the written ones (`KeyPins m`,
Pins.lean), `treesSent` returns, at the key file's three chains, the named values `treesOf
keySends0 1 []`, `treesOf keySends1 0 masksB`, `treesOf keySends2 0 []`, whichever text is handed
to it for the wording of a refusal. No return of a routine stands among its premises.
Limits. THAT `KeyPins` HOLDS AT ANY m IS NOT SHOWN HERE. `treesOf` is a term, not a written list;
TreesAtKey.lean brings it to a form that the kernel can evaluate.
Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.FitsA
import Johnson.AtFull.KeyBack.FitsB
import Johnson.AtFull.KeyBack.FitsC
import Johnson.AtFull.KeyBack.Pins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open Johnson.G.OfPlan
open Johnson.G (keySends0 keySends1 keySends2)

/-- **The core from the pins alone.** -/
theorem treesK_at_pins (m : Made) (h : KeyPins m) :
    TreesK m (treesOf keySends0 1 []) (treesOf keySends1 0 masksB) (treesOf keySends2 0 []) := by
  have h0 : m.key.1 = keySends0 := by rw [h.sends]
  have h1 : m.key.2.1 = keySends1 := by rw [h.sends]
  have h2 : m.key.2.2 = keySends2 := by rw [h.sends]
  have t := treesK_of_fits m 1 0 0 (by rw [h0, h.p₀]; exact fits_A)
    (by rw [h1, h.p₁, h.shape]; exact fits_B) (by rw [h2, h.p₂]; exact fits_C)
  rw [h0, h1, h2, h.p₁, h.shape] at t
  exact t

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.treesK_at_pins
