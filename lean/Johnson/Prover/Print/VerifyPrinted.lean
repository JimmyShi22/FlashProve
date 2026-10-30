-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/VerifyPrinted.lean: the goals' verify at the form that is printed of a whole
typed proof (`formOf`, Johnson/Prover/Print/Form.lean) evaluates, at every hash function, to the
typed verifier's own answer at that typed proof.

Main names (namespace `Johnson.Prover.Print`).
  `verify_formOf`      at files in scope, at every hash function, with c the digest that the parser
      draws (cAt Z hash) as bytes: PublicS (S Z) → Fits (S Z) c q → verify at formOf (S Z) q
      evaluates to `verifyVDet` (Johnson/Top/Fire/Code/VerifyVDet.lean) at q's nine parts
  `innerCompiledVerifier_formOf`   the same end at `innerCompiledVerifier`, at the typed proof of the form that the decoder
      gives

By: `decodeD_formOf` (Johnson/Prover/Print/FormBack.lean) and `verify_of_decode`,
`innerCompiledVerifier_of_decode` (Johnson/Prover/Print/VerifyForm.lean).

Limits. An equation: nothing here says that the typed verifier says yes anywhere. `Fits` is asked at
the digest that is drawn under the same hash function; that an honest side's parts meet it there,
and the description's letters `PublicS`, is not shown here. No goal is stated. Nothing on soundness
or completeness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Print.FormBack
import Johnson.Prover.Print.VerifyForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Print

open VerifierAndGoals FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open _root_.Run (digToBytes)

variable (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (f₀ : DecodedProof) (Hb : CommitterAndProver FormBytes)

/-- **verify at a printed form is the typed verifier's answer at the typed proof.** -/
theorem verify_formOf (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    (hash : VerifiableInference.Hash) (commitment : Commitment) (prompt output : List Token)
    (q : Typed (S Z)) (hS : PublicS (S Z)) (hq : Fits (S Z) (digToBytes (cAt Z hash)) q) :
    (VerifierAndGoals.verify (descriptionOnBytes S f₀ Hb) Z ((descriptionOnBytes S f₀ Hb).parse Z) commitment prompt output
        (formOf (S Z) q)).evaluate hash =
      verifyVDet (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings (cAt Z hash) (sevenAt Z hash))).toInputV hash
        commitment prompt output
        (q.aux, ⟨q.cm, q.rcd⟩, ⟨q.copy, some q.piT, (q.cm', q.rcd', some q.piL), some q.piB⟩) := by
  obtain ⟨f, hd, hp⟩ := decodeD_formOf (S Z) (digToBytes (cAt Z hash)) q hS hq
  rw [verify_of_decode S f₀ Hb Z scope hash commitment prompt output _ f hd, hp]
  rfl

/-- The same end at `innerCompiledVerifier`. -/
theorem innerCompiledVerifier_formOf (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    (hash : VerifiableInference.Hash) (commitment : Commitment) (prompt output : List Token)
    (q : Typed (S Z)) (hS : PublicS (S Z)) (hq : Fits (S Z) (digToBytes (cAt Z hash)) q) :
    ∃ f : DecodedProof, decodeD (digToBytes (cAt Z hash)) (formOf (S Z) q) = some f ∧
      (S Z).proofOf (digToBytes (cAt Z hash)) f =
        (q.aux, ⟨q.cm, q.rcd⟩, ⟨q.copy, some q.piT, (q.cm', q.rcd', some q.piL), some q.piB⟩) ∧
      (VerifierAndGoals.verify (descriptionOnBytes S f₀ Hb) Z ((descriptionOnBytes S f₀ Hb).parse Z) commitment prompt output
          (formOf (S Z) q)).evaluate hash =
        (innerCompiledVerifier (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings (cAt Z hash) (sevenAt Z hash))) commitment prompt
          output ((S Z).typedOf (digToBytes (cAt Z hash)) f)).evaluate hash := by
  obtain ⟨f, hd, hp⟩ := decodeD_formOf (S Z) (digToBytes (cAt Z hash)) q hS hq
  exact ⟨f, hd, hp, innerCompiledVerifier_of_decode S f₀ Hb Z scope hash commitment prompt output _ f hd⟩

end Johnson.Prover.Print
