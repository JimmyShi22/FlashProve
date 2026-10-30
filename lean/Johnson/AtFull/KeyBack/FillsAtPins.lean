-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/FillsAtPins.lean: the seven tests behind `declKOf`, at an m whose plans and
shape are the full size's written ones, from one closed Bool.

By one call of `fillsK_of` (FillsBool.lean), at the pins (`KeyPins`, Pins.lean) and at the three
closed counts (`draws_at0`, `draws_at1`, `draws_at2`: DrawsAt0.lean, DrawsAt1.lean, DrawsAt2.lean).

Limits. That `KeyPins` holds at any m is not shown. That `fillsB` says yes at any lists of trees is
not shown: it can be evaluated only where the three lists are written values. Nothing on soundness,
nothing on hiding.

-/
import Johnson.AtFull.KeyBack.FillsBool
import Johnson.AtFull.KeyBack.Pins
import Johnson.AtFull.KeyBack.DrawsAt0
import Johnson.AtFull.KeyBack.DrawsAt1
import Johnson.AtFull.KeyBack.DrawsAt2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open Johnson.G.OfPlan
open Lk6.AtPlan (keyFull)

/-- **`FillsK` at a pinned m, from one closed Bool.** -/
theorem fillsK_at (m : Made) (h : KeyPins m) (t₀ t₁ t₂ : List (Sent × Nat))
    (hB : fillsB 4 10 5 keyFull.once.shape t₀ t₁ t₂ = true) : FillsK m t₀ t₁ t₂ :=
  fillsK_of m _ _ _ _ 4 10 5 t₀ t₁ t₂ h.p₀ h.p₁ h.p₂ h.shape draws_at0 draws_at1 draws_at2 hB

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.fillsK_at
