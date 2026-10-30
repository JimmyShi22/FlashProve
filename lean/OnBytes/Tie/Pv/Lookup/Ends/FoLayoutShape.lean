-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLayoutShape.lean: the shape of the layers' one lookup is made of the
layout's own calls.

Layer.layoutLook (OnBytes/Model/LayerLayout.lean) makes the calls' records cl, runs Forest.shape on
them, counts the padding keys pub, asks Forest.pubAsk of them, and stores cl and the shape with pub
laid in. This file reads that off a run of layoutLook that returns.

Main names:
  `layoutLook_h`: layoutLook keeps the field h.
  `layoutLook_shape`: Layer.layoutLook y = .ok y' gives ShapeOf y'.cl y'.fo.pub y.h.lidb y'.fo
    (`ShapeOf`, OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean): the shape y'.fo is what Forest.shape makes
    of y'.cl at y.h.lidb, with y'.fo.pub laid in, and Forest.pubAsk has passed.

Limits: one direction: from a run that returns. Nothing on what the calls are.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Port.FoHeard
import OnBytes.Model.LayerLayout

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model

private theorem bindX {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem layoutLook_h {y y' : Layer.Lay} (e : Layer.layoutLook y = .ok y') : y'.h = y.h := by
  unfold Layer.layoutLook at e
  dsimp only at e
  obtain ⟨_, _, e⟩ := bindX e
  obtain ⟨fo, _, e⟩ := bindX e
  obtain ⟨_, _, e⟩ := bindX e
  obtain ⟨kbm, _, e⟩ := bindX e
  obtain ⟨_, _, e⟩ := bindX e
  obtain ⟨pub, _, e⟩ := bindX e
  obtain ⟨_, _, e⟩ := bindX e
  obtain ⟨_, _, e⟩ := bindX e
  cases e
  rfl

/-- **The layers' lookup: its shape is made of the layout's own calls.** -/
theorem layoutLook_shape {y y' : Layer.Lay} (e : Layer.layoutLook y = .ok y') :
    ShapeOf y'.cl y'.fo.pub y.h.lidb y'.fo := by
  unfold Layer.layoutLook at e
  dsimp only at e
  obtain ⟨_, _, e⟩ := bindX e
  obtain ⟨fo, hf, e⟩ := bindX e
  obtain ⟨_, _, e⟩ := bindX e
  obtain ⟨kbm, _, e⟩ := bindX e
  obtain ⟨_, _, e⟩ := bindX e
  obtain ⟨pub, _, e⟩ := bindX e
  obtain ⟨_, hp, e⟩ := bindX e
  obtain ⟨_, _, e⟩ := bindX e
  cases e
  exact ⟨fo, hf, hp, rfl⟩

end Fo
