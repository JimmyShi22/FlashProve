-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/OneOmegaB.lean: no soundness is claimed.
OneOmega (OmegaDeclared.lean) as a test with code, so that a file of evaluations can evaluate it at a plan and the yes is the premise by Lean, not by reading.
  oneOmegaB π nΩ     every opening that the block's declared rounds name under «taken c n» has c ≠ 1 or n = nΩ
  oneOmega_iff       oneOmegaB π nΩ = true ↔ OneOmega π nΩ
-/
import Johnson.ToldDescR.OmegaDeclared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open VerifiableInference.Desc VerifiableInference.Desc.K12

def oneOmegaB (π : P12) (nΩ : ℕ) : Bool :=
  ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).rounds.flatMap (·.opens)).all fun x =>
    match x.2 with
    | .own _ => true
    | .taken c n => c != 1 || n == nΩ

theorem oneOmega_iff (π : P12) (nΩ : ℕ) : oneOmegaB π nΩ = true ↔ OneOmega π nΩ := by
  unfold oneOmegaB OneOmega
  rw [List.all_eq_true]
  constructor
  · intro h r hr x hx n e
    have h1 := h x (List.mem_flatMap.2 ⟨r, hr, hx⟩)
    rw [e] at h1
    simpa using h1
  · intro h x hx
    obtain ⟨r, hr, hx'⟩ := List.mem_flatMap.1 hx
    cases e : x.2 with
    | own _ => rfl
    | taken c n =>
      by_cases hc : c = 1
      · subst hc
        have := h r hr x hx' n e
        simp [this]
      · simp [hc]

end ToldDesc

#print axioms ToldDesc.oneOmega_iff
