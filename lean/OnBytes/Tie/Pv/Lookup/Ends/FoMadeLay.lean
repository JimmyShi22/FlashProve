-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoMadeLay.lean: each of the three layouts lays down, as its record of the
lookup's numbers, what Forest.shape makes of the calls that it lays down beside it.

Fo.Made calls lid fs (OnBytes/Tie/Pv/Lookup/Ends/FoShapes.lean): Forest.shape calls lid returns some
h0, and fs is h0 with fs's own numbers of padding keys.

 - made_layoutLook, made_layout: where Layer.layoutLook, Layer.layout return y: Made y.cl y.h.lidb
   y.fo.
 - made_shapeHid: where Attention.shapeHid lid cf returns (S, fs): Made (the calls of S) lid fs.
 - made_headLayout: where Head.layout h tauFC returns L: Made L.cl h.LIDB L.fs.
The last two by shape_iota (OnBytes/Tie/Pv/Lookup/Ends/FoShapeIota.lean): these layouts run
Forest.shape before they lay iota into each call.

Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that a layout returns.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoShapeIota

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.Ends OnBytes.PscRun

/-- The layers' layout. -/
theorem made_layoutLook {y y' : Layer.Lay} (e : Layer.layoutLook y = .ok y') :
    Made y'.cl y'.h.lidb y'.fo := by
  unfold Layer.layoutLook at e
  dsimp only at e
  obtain ⟨_, _, e⟩ := ok_of_bind e
  obtain ⟨fo, hs, e⟩ := ok_of_bind e
  obtain ⟨_, _, e⟩ := ok_of_bind e
  obtain ⟨kbm, _, e⟩ := ok_of_bind e
  obtain ⟨_, _, e⟩ := ok_of_bind e
  obtain ⟨pub, _, e⟩ := ok_of_bind e
  obtain ⟨_, _, e⟩ := ok_of_bind e
  obtain ⟨_, _, e⟩ := ok_of_bind e
  cases e
  exact ⟨fo, hs, rfl⟩

theorem made_layout {h : Layer.Shape} {pc : List (List String)} {y : Layer.Lay}
    (e : Layer.layout h pc = .ok y) : Made y.cl y.h.lidb y.fo := by
  unfold Layer.layout at e
  obtain ⟨y0, _, e⟩ := ok_of_bind e
  exact made_layoutLook e

/-- Attention's shape. -/
theorem made_shapeHid {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Forest.Shape}
    (e : Attention.shapeHid lid cf = .ok (S, fs)) : Made (S.calls.map (·.call)) lid fs := by
  unfold Attention.shapeHid at e
  obtain ⟨A, _, e⟩ := ok_of_bind e
  obtain ⟨h, hs, e⟩ := ok_of_bind e
  obtain ⟨_, _, e⟩ := ok_of_bind e
  obtain ⟨kbA, _, e⟩ := ok_of_bind e
  dsimp only at e
  obtain ⟨counted, _, e⟩ := ok_of_bind e
  obtain ⟨_, _, e⟩ := ok_of_bind e
  cases e
  refine ⟨_, shape_iota ?_ hs, rfl⟩
  apply Array.ext <;> simp [strip]

/-- The head's layout. -/
theorem made_headLayout {h : Head.Shape} {tauFC : Array F} {L : Head.HL}
    (e : Head.layout h tauFC = .ok L) : Made L.cl h.LIDB L.fs := by
  unfold Head.layout at e
  obtain ⟨_, _, e⟩ := ok_of_bind e
  obtain ⟨_, _, e⟩ := ok_of_bind e
  obtain ⟨L0, _, e⟩ := ok_of_bind e
  obtain ⟨calls, _, e⟩ := ok_of_bind e
  dsimp only at e
  obtain ⟨_, _, e⟩ := ok_of_bind e
  obtain ⟨_, _, e⟩ := ok_of_bind e
  obtain ⟨fs, hs, e⟩ := ok_of_bind e
  obtain ⟨_, _, e⟩ := ok_of_bind e
  obtain ⟨kb, _, e⟩ := ok_of_bind e
  obtain ⟨_, _, e⟩ := ok_of_bind e
  obtain ⟨pub, _, e⟩ := ok_of_bind e
  obtain ⟨_, _, e⟩ := ok_of_bind e
  obtain ⟨_, _, e⟩ := ok_of_bind e
  obtain ⟨_, _, e⟩ := ok_of_bind e
  obtain rfl := Except.ok.inj e
  refine ⟨_, shape_iota ?_ hs, rfl⟩
  apply Array.ext <;> simp [strip]

end Fo
