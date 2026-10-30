-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Print/YesOfVra.lean: from the yes of the compiled verifier at a whole typed proof to
the yes of the goals' verify at the form that is printed of it.

Main names (namespace `Johnson.Prover.Print`).
  `yes_of_vra`   at files in scope, at every hash function; r the input at the two public readings
      under that hash function, c the drawn digest as bytes: PublicS (S Z) → Fits (S Z) c q → the
      instance is built of (prompt, output) and q's further tokens → the key (q.cm, q.rcd) has a
      code → `verifyAtKeyRoot` at that key, that instance and q's proof says yes under the typed oracle
      functions that are read off the hash function → verify evaluates to true, at the commitment
      that the hash function gives at the code, and at the form `formOf (S Z) q`

By: `innerCompiledVerifier_formOf` (Johnson/Prover/Print/VerifyPrinted.lean), `innerCompiledVerifier_yes_of`
(Johnson/Top/InnerCompiledVerifierYesBack.lean), and the text of `DescriptionDataAtFiles.typedOf` (Johnson/Goal/Tie/DescriptionOnDecodedProof.lean).

Limits. No probability. Each premise is asked, none is shown here: above all that `verifyAtKeyRoot` says yes. No
goal is stated. Nothing on soundness or completeness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Print.VerifyPrinted
import Johnson.Top.InnerCompiledVerifierYesBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Print

open VerifierAndGoals FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open TypedOracleCompiler.Compile.Batch.Cms (verifyAtKeyRoot)
open _root_.Run (digToBytes)

variable (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (f₀ : DecodedProof) (Hb : CommitterAndProver FormBytes)

/-- **The compiled verifier's yes at a whole typed proof gives verify's yes at its printed
form.** -/
theorem yes_of_vra (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true) (hash : VerifiableInference.Hash)
    (prompt output : List Token) (q : Typed (S Z)) (hS : PublicS (S Z))
    (hq : Fits (S Z) (digToBytes (cAt Z hash)) q)
    (x : (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings (cAt Z hash) (sevenAt Z hash))).Instance) (code : ZKCP.Str)
    (hb : (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings (cAt Z hash) (sevenAt Z hash))).buildInstance (prompt, output) q.aux =
      some x)
    (he : (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings (cAt Z hash) (sevenAt Z hash))).keyCode ⟨q.cm, q.rcd⟩ = some code)
    (hv : (verifyAtKeyRoot (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings (cAt Z hash) (sevenAt Z hash))).queryLayout
        (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings (cAt Z hash) (sevenAt Z hash))).seedQueries
        (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings (cAt Z hash) (sevenAt Z hash))).answerCode
        (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings (cAt Z hash) (sevenAt Z hash))).fixedSample
        (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings (cAt Z hash) (sevenAt Z hash))).compilerParameters ⟨q.cm, q.rcd⟩ x
        ⟨q.copy, some q.piT, (q.cm', q.rcd', some q.piL), some q.piB⟩).det
      (Rom.readBlocks (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings (cAt Z hash) (sevenAt Z hash))).oracleCoding
        (_root_.Run.famOne hash)) = true) :
    (VerifierAndGoals.verify (descriptionOnBytes S f₀ Hb) Z ((descriptionOnBytes S f₀ Hb).parse Z) (hash code) prompt output
      (formOf (S Z) q)).evaluate hash = true := by
  obtain ⟨f, -, hp, hy⟩ := innerCompiledVerifier_formOf S f₀ Hb Z scope hash (hash code) prompt output q hS hq
  rw [hy]
  have ht : (S Z).typedOf (digToBytes (cAt Z hash)) f =
      (q.aux, ⟨q.cm, q.rcd⟩, ⟨q.copy, some q.piT, (q.cm', q.rcd', some q.piL), some q.piB⟩) := by
    unfold DescriptionDataAtFiles.typedOf
    rw [hp]
    rfl
  rw [ht]
  exact innerCompiledVerifier_yes_of _ hash (hash code) prompt output _ hb he rfl hv

end Johnson.Prover.Print
