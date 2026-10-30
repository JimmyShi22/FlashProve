-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/SourceAtPins.lean: `Key.sourceOf m` returns at an m whose plans and shape are
the full size's written ones, and its declared rounds are the written declared rounds.

Calls alone: `fillsK_at` (FillsAtPins.lean), `sourceOf_at` (SourceReturns.lean), `declK_at`
(DeclCloser.lean).

Limits. It takes a return to give a return: `TreesK` is three returns. Neither `KeyPins` nor
`TreesK` is shown at any m, and neither `fillsB` nor `closesB` at any lists of trees. So that
`sourceOf` returns at any m is not shown here. Of T only that it is returned. Nothing on soundness,
nothing on hiding.

-/
import Johnson.AtFull.KeyBack.FillsAtPins
import Johnson.AtFull.KeyBack.SourceReturns
import Johnson.AtFull.KeyBack.DeclCloser

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key
open Johnson.KB8 (declKeyFull)
open Lk6.AtPlan (keyFull)

/-- **`sourceOf` at a pinned m**: its declared rounds are the written value. -/
theorem sourceOf_at_pins (m : Made) (h : KeyPins m) (t₀ t₁ t₂ : List (Sent × Nat))
    (hT : TreesK m t₀ t₁ t₂) (hB : fillsB 4 10 5 keyFull.once.shape t₀ t₁ t₂ = true)
    (hC : closesB keyFull.once.shape t₀ t₁ t₂ = true) :
    ∃ T, toldOfMade m = .ok T ∧ sourceOf m = .ok (sourceAt m declKeyFull T) := by
  have hs := sourceOf_at m t₀ t₁ t₂ hT (fillsK_at m h t₀ t₁ t₂ hB)
  rw [declK_at m h t₀ t₁ t₂ hC] at hs
  exact hs

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.sourceOf_at_pins
