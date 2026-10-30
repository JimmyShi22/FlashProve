-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/FitsOf.lean: fits_of_eq: if T.at (pair c m) = D.input Z c m for all values c and m
of the types of VerifierAndGoals.verify's two readings, whether or not these can return them, then innerCompiledVerifier
at the one input equals innerCompiledVerifier at the other, at every commitment, prompt, output and typed proof.
This is the premise fits of Shell.lean.
Terms and the limits that go with any quote: Spec.lean.

Limits. An equation of two terms: nothing on whether either accepts.

How it fits. AtDescription.lean, Joined.lean and FromPremises.lean use it.
-/
import Johnson.PV.FitO

set_option autoImplicit false

noncomputable section

namespace OnBytes.FrontRoad
open VerifiableInference VerifiableInference.OnPublicFiles VerifierAndGoals

/-- If T.at (pair c m) = D.input Z c m for all c and m, then innerCompiledVerifier at D.input Z c m equals
innerCompiledVerifier at T.at (pair c m), at every commitment, prompt, output and typed proof. -/
theorem fits_of_eq (D : Description) (Z : VerifierAndGoals.PublicFiles) (c₀ : Digest) (m₀ : D.More)
    (T : LayoutsByPublicReading (D.input Z c₀ m₀)) (pair : Digest → D.More → T.D)
    (eq : ∀ c m, T.at (pair c m) = D.input Z c m) :
    ∀ c m commitment prompt output (proof : TypedProof (D.F Z) (D.P Z)),
      innerCompiledVerifier (D.input Z c m) commitment prompt output proof =
        innerCompiledVerifier (T.at (pair c m)) commitment prompt output proof := by
  intro c m commitment prompt output proof
  have h : HEq (innerCompiledVerifier (D.input Z c m)) (innerCompiledVerifier (T.at (pair c m))) := by rw [eq c m]
  exact congrFun (congrFun (congrFun (congrFun (eq_of_heq h) commitment) prompt) output) proof

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.fits_of_eq
