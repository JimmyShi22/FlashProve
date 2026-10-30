-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/CastD.lean: four short theorems more on `Maps.castD`
(OnBytes/Flat/KindsRow.lean: a list of maps carried along an equation e : ds' = ds of lists of
written rounds; `ok_castD`, `held_castD`, `heldN_castD` stand there): its written counts, its image
and its tests of work.

Why. A piece (Johnson/Desc/Sound/ChainRule.lean) holds its written rounds as a list of its own, the
field ds; the maps of a chain are
typed with the list from which they were made. Where the two lists are shown equal, the maps are
wanted at the piece's, with what they do to a transcript.

  `err_castD`: the written counts are M's, carried along. `le_castD`: they lie below counts x if M's
  lie below x carried back. `view_castD`, `pass_castD`: the image and the tests of work on a
  transcript are M's on the transcript carried back.

Limits. Bookkeeping along an equation: each proof replaces one list by the
other.
-/
import OnBytes.Flat.KindsRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Flat
open Iop Run OnBytes.Maker

namespace Maps

variable {ds ds' : List RDT} {s' : Shape}

/-- The written counts: those of M, carried along. -/
theorem err_castD (e : ds' = ds) (M : Maps ds s') (δ : Err s') :
    (M.castD e).err δ = e ▸ M.err δ := by
  subst e
  rfl

/-- They lie below counts x if M's lie below x carried back. -/
theorem le_castD (e : ds' = ds) (M : Maps ds s') (δ : Err s') (x : Err (uLT (ckP .two) ds'))
    (hle : Err.le (M.err δ) (e ▸ x)) : Err.le ((M.castD e).err δ) x := by
  subst e
  exact hle

/-- The image: that of M on the transcript carried back. -/
theorem view_castD (e : ds' = ds) (M : Maps ds s') (τ : Tr (uLT (ckP .two) ds')) :
    (M.castD e).view τ = M.view (e ▸ τ) := by
  subst e
  rfl

/-- The tests of work: those of M on the transcript carried back. -/
theorem pass_castD (e : ds' = ds) (M : Maps ds s') (τ : Tr (uLT (ckP .two) ds')) :
    (M.castD e).pass τ = M.pass (e ▸ τ) := by
  subst e
  rfl

end Maps
end OnBytes.Flat

#print axioms OnBytes.Flat.Maps.err_castD
#print axioms OnBytes.Flat.Maps.le_castD
#print axioms OnBytes.Flat.Maps.view_castD
#print axioms OnBytes.Flat.Maps.pass_castD
