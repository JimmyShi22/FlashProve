-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/Sim/RestKinds.lean: WHAT STANDS BEHIND THE SIX IN THE SHARED FIELD IS OF KIND K12, by the two places that AtFullSide/K12/ReturnsAtFillW.lean gives (`halfU_place`, `halfO_place`).

  `rest_kind`      **every half of the two is of kind K12**: so no half behind the six is of kind K14 or K1

No property of the protocol is claimed.
-/
import AtFullSide.K12.ReturnsAtFillW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof

/-- **Every half behind the six is of kind K12.** -/
theorem rest_kind {W₀ : Type} (wt : W₀ → Weights)
    (enc : W₀ → IndexCommitterCoins → ℕ → ℕ → Option (List Cb.Gl.F)) (Z : Pub) :
    ∀ x ∈ halfU wt enc Z ++ halfO wt Z, x.place.kind = .K12 := by
  intro x hx
  rcases List.mem_append.1 hx with h | h
  · rw [AtFullSide.K12.halfU_place wt enc Z x h]
    rfl
  · rw [AtFullSide.K12.halfO_place wt Z x h]
    rfl

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.rest_kind
