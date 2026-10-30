-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/VerifyForm.lean: THE GOALS' verify AT A FORM THAT THE DECODER TAKES IS THE
TYPED VERIFIER's OWN ANSWER AT THE TYPED PROOF THAT IS LAID OF IT: AT EVERY HASH FUNCTION.

Why. verify_descriptionOnBytes (Johnson/Goal/Tie/DescriptionOnBytes.lean) says the like at hash functions of the
form hashOf O alone. Completeness integrates over all hash functions.

Main names.
  innerCompiledVerifier_of_decode   the same with the end at innerCompiledVerifier … ((S Z).typedOf c f): the form in which
    the typed system's own theorems speak.
  verify_of_decode   at files in scope, at every hash function: with c the digest that the parser
    draws (cAt Z hash) as bytes: if decodeD c B = some f, then verify at the form B evaluates to
    verifyVDet (Johnson/Top/Fire/Code/VerifyVDet.lean) at the proof (S Z).proofOf c f: build · the
    key's code hashed against the commitment · the compiled verifier's value under the typed oracle
    functions that are read off the hash function.

By: verify_descriptionOfFields (Johnson/Goal/Tie/DescribeT.lean) · the parser's text · typedOf_back ·
verifyV_toInputV (Johnson/Top/InnerCompiledVerifierBack.lean) · verifyVDet_is
(Johnson/Top/Fire/Code/VerifyVDetProbe.lean).

Not shown here: that a form is taken by the decoder (Johnson/Prover/Print/FormBack.lean shows it of
a printed form); that verifyVDet says yes anywhere. Nothing on soundness or completeness. It
names no goal's form.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Tie.DescriptionOnBytes
import Johnson.Top.InnerCompiledVerifierBack
import Johnson.Top.Fire.Code.VerifyVDetProbe

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Print

open VerifierAndGoals FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open _root_.Run (digToBytes)

variable (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (f₀ : DecodedProof) (Hb : CommitterAndProver FormBytes)

/-- **verify at a form that the decoder takes, at every hash function: the end at innerCompiledVerifier.** -/
theorem innerCompiledVerifier_of_decode (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    (hash : VerifiableInference.Hash) (commitment : Commitment) (prompt output : List Token)
    (B : FormBytes) (f : DecodedProof) (hdec : decodeD (digToBytes (cAt Z hash)) B = some f) :
    (VerifierAndGoals.verify (descriptionOnBytes S f₀ Hb) Z ((descriptionOnBytes S f₀ Hb).parse Z) commitment prompt output
        B).evaluate hash =
      (innerCompiledVerifier (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings (cAt Z hash) (sevenAt Z hash))) commitment prompt
        output ((S Z).typedOf (digToBytes (cAt Z hash)) f)).evaluate hash := by
  have h1 := verify_descriptionOfFields (fun Z => (S Z).toDescriptionFields) (committerAndProverWithParser S Hb decodeD f₀) Z
    ((descriptionOnBytes S f₀ Hb).parse Z) scope hash commitment prompt output B
  have h2 : proofAt ((descriptionOnBytes S f₀ Hb).parse Z) prompt output B hash =
      (S Z).typedOf (digToBytes (cAt Z hash)) f := by
    show (S Z).typedOf (digToBytes (cAt Z hash))
      ((decodeD (digToBytes (cAt Z hash)) B).getD f₀) = _
    rw [hdec]
    rfl
  exact h1.trans (congrArg (fun q : (S Z).Typed =>
    (innerCompiledVerifier (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings (cAt Z hash) (sevenAt Z hash))) commitment prompt output
      q).evaluate hash) h2)

/-- **The same, the end at the verifier's side's own form.** -/
theorem verify_of_decode (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    (hash : VerifiableInference.Hash) (commitment : Commitment) (prompt output : List Token)
    (B : FormBytes) (f : DecodedProof) (hdec : decodeD (digToBytes (cAt Z hash)) B = some f) :
    (VerifierAndGoals.verify (descriptionOnBytes S f₀ Hb) Z ((descriptionOnBytes S f₀ Hb).parse Z) commitment prompt output
        B).evaluate hash =
      verifyVDet (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings (cAt Z hash) (sevenAt Z hash))).toInputV hash
        commitment prompt output ((S Z).proofOf (digToBytes (cAt Z hash)) f) := by
  have h13 := innerCompiledVerifier_of_decode S f₀ Hb Z scope hash commitment prompt output B f hdec
  have h4 := verifyV_toInputV (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings (cAt Z hash) (sevenAt Z hash)))
    commitment prompt output ((S Z).proofOf (digToBytes (cAt Z hash)) f)
  have h5 := verifyVDet_is (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings (cAt Z hash) (sevenAt Z hash))).toInputV hash
    commitment prompt output ((S Z).proofOf (digToBytes (cAt Z hash)) f)
  rw [h4] at h5
  exact h13.trans h5

end Johnson.Prover.Print

#print axioms Johnson.Prover.Print.innerCompiledVerifier_of_decode
#print axioms Johnson.Prover.Print.verify_of_decode
