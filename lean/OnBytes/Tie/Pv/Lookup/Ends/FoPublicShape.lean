-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPublicShape.lean: in the public record, the shape of the layers' one
lookup is made of the layout's own calls.

It carries layoutLook_shape (OnBytes/Tie/Pv/Lookup/Ends/FoLayoutShape.lean) up to the record X that
Verify.publicOf returns.

Main names:
  `layout_shape`: Layer.layout h pc = .ok y gives ShapeOf y.cl y.fo.pub y.h.lidb y.fo.
  `polLayout_shape`: the same from Verify.polLayout pol = .ok (P, y).
  `public_shape`: Verify.publicOf pol KL layout = .ok X gives it at y := X.layers.y.

Limits: one direction: from a run that returns. Nothing on what the calls are.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLayoutShape
import OnBytes.Tie.Pv.Lookup.Ends.FoPublic

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model Fo.BatRows

theorem layout_shape {h : Layer.Shape} {pc : List (List String)} {y : Layer.Lay}
    (e : Layer.layout h pc = .ok y) : ShapeOf y.cl y.fo.pub y.h.lidb y.fo := by
  unfold Layer.layout at e
  obtain ⟨y0, _, e⟩ := bindE_ok e
  rw [layoutLook_h e]
  exact layoutLook_shape e

theorem polLayout_shape {pol : ByteArray} {P : PolScan} {y : Layer.Lay}
    (e : Verify.polLayout pol = .ok (P, y)) : ShapeOf y.cl y.fo.pub y.h.lidb y.fo := by
  unfold Verify.polLayout at e
  obtain ⟨P0, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨y0, hy, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  cases e
  exact layout_shape hy

/-- **The public record: the layers' lookup's shape is made of the layout's own calls.** -/
theorem public_shape {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) :
    ShapeOf X.layers.y.cl X.layers.y.fo.pub X.layers.y.h.lidb X.layers.y.fo :=
  polLayout_shape (Pub.publicOf_cut pol KL layout X h).1

end Fo
