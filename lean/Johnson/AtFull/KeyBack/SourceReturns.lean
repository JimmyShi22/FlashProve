-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/SourceReturns.lean: `Key.sourceOf m` returns, from the three returns of
`treesSent` at the key file's chains and seven tests.

Calls alone: `sourceOf_iff` (SourceIs.lean), `declKOf_returns` (FillOpens.lean) and
`toldOfMade_returns` (ToldLaw.lean).

  `sourceOf_at`: the answer is `sourceAt m (declK m t₀ t₁ t₂) T`, where T is what `toldOfMade m`
    returns.
  `sourceOf_returns`: so `sourceOf m` returns.

Limits. It takes a return to give a return: `TreesK` is three returns, and neither `TreesK` nor
`FillsK` is shown at any m. So that `sourceOf` returns at any m is not shown here. Of T only that it
is returned: which tenants and which groups it holds is not said.
Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.FillOpens
import Johnson.AtFull.KeyBack.SourceIs
import Johnson.AtFull.KeyBack.ToldLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key

/-- **`sourceOf` returns, and what**: its declared rounds are `declK`'s. -/
theorem sourceOf_at (m : Made) (t₀ t₁ t₂ : List (Sent × Nat)) (hT : TreesK m t₀ t₁ t₂)
    (hF : FillsK m t₀ t₁ t₂) :
    ∃ T, toldOfMade m = .ok T ∧ sourceOf m = .ok (sourceAt m (declK m t₀ t₁ t₂) T) := by
  obtain ⟨T, hTold⟩ := toldOfMade_returns m t₀ t₁ t₂ hT
  exact ⟨T, hTold,
    (sourceOf_iff m _).2 ⟨_, T, declKOf_returns m t₀ t₁ t₂ hT hF, hTold, rfl⟩⟩

/-- So `sourceOf` returns. -/
theorem sourceOf_returns (m : Made) (t₀ t₁ t₂ : List (Sent × Nat)) (hT : TreesK m t₀ t₁ t₂)
    (hF : FillsK m t₀ t₁ t₂) : ∃ X, sourceOf m = .ok X := by
  obtain ⟨T, _, h⟩ := sourceOf_at m t₀ t₁ t₂ hT hF
  exact ⟨_, h⟩

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.sourceOf_at
#print axioms Johnson.AtFull.KeyBack.sourceOf_returns
