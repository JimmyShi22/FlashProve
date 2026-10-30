-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/At/YesTold.lean: `yes_of_vra` (Johnson/Prover/Print/YesOfVra.lean) in the letters of
the told record (`DescriptionDataAtFiles.layoutsByPublicReading`, Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean): from the yes of the compiled
verifier at the told record's seeds, answers' code and coding at the public reading under a hash
function, to the yes of the goals' verify at the printed form, at the commitment that is the digest
of the key with the told part.

Main names (namespace `Johnson.Prover.Print`).
  `yes_of_vra_told`   R the told record's ground input, T the told record, d the pair
      (cAt Z hash, sevenAt Z hash): PublicS → Fits at the drawn digest → R.buildInstance (prompt, output)
      q.aux = some x → `verifyAtKeyRoot` R.queryLayout (T.Sd d) (T.cA d) R.fixedSample R.compilerParameters at q's key, x and q's proof says yes
      under `readBlocks (T.m d) (famOne hash)` → verify evaluates to true at the commitment
      `digestUnder hash T.encT (T.part d, key)` and the form `formOf (S Z) q`

By: `innerCompiledVerifier_formOf` (Johnson/Prover/Print/VerifyPrinted.lean), `LPFD.Full.fitsD`
(Johnson/Flat/Told/Dec/TAtLaws.lean: innerCompiledVerifier at the input at d is innerCompiledVerifier at the record's input
at d), `innerCompiledVerifier_yes_of` (Johnson/Top/InnerCompiledVerifierYesBack.lean) at the record's input at d, and
`layoutsByPublicReading_total` (every pair of a told part and a key has a code).

Limits. No probability. Each premise is asked, none is shown here. No goal is stated. Nothing on
soundness or completeness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Print.YesOfVra
import Johnson.Flat.Told.Dec.LayoutsAtDescriptionOfFields

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Print

open VerifierAndGoals FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open TypedOracleCompiler.Compile.Batch.Cms (verifyAtKeyRoot)
open _root_.Run (digToBytes)
open _root_.Iop (Dig)

/- Lean compares these names and does not unfold them (as in Johnson/Flat/Told/Dec/LayoutsAtDescriptionDataAtFiles.lean). -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8

variable (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (f₀ : DecodedProof) (Hb : CommitterAndProver FormBytes)
  (c₀ : Digest) (m₀ : List (Dig 256))

set_option maxRecDepth 20000 in
/-- **The compiled verifier's yes in the told record's letters gives verify's yes at the printed
form.** -/
theorem yes_of_vra_told (Z : PublicFiles) (scope : VerifierAndGoals.InScope Z = true)
    (hash : VerifiableInference.Hash) (prompt output : List Token) (q : Typed (S Z))
    (hS : PublicS (S Z)) (hq : Fits (S Z) (digToBytes (cAt Z hash)) q)
    (x : (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings c₀ m₀)).Instance)
    (hb : (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings c₀ m₀)).buildInstance (prompt, output) q.aux = some x)
    (hv : (verifyAtKeyRoot (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings c₀ m₀)).queryLayout
        (((S Z).layoutsByPublicReading c₀ m₀).Sd (cAt Z hash, sevenAt Z hash))
        (((S Z).layoutsByPublicReading c₀ m₀).cA (cAt Z hash, sevenAt Z hash))
        (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings c₀ m₀)).fixedSample (innerCompilerInputAtFullSize ((S Z).inputFieldsAtReadings c₀ m₀)).compilerParameters
        ⟨q.cm, q.rcd⟩ x ⟨q.copy, some q.piT, (q.cm', q.rcd', some q.piL), some q.piB⟩).det
      (Rom.readBlocks (((S Z).layoutsByPublicReading c₀ m₀).m (cAt Z hash, sevenAt Z hash))
        (_root_.Run.famOne hash)) = true) :
    (VerifierAndGoals.verify (descriptionOnBytes S f₀ Hb) Z ((descriptionOnBytes S f₀ Hb).parse Z)
      (ZKCP.digestUnder hash ((S Z).layoutsByPublicReading c₀ m₀).encT
        (((S Z).layoutsByPublicReading c₀ m₀).part (cAt Z hash, sevenAt Z hash), ⟨q.cm, q.rcd⟩))
      prompt output (formOf (S Z) q)).evaluate hash = true := by
  obtain ⟨code, he⟩ := Option.ne_none_iff_exists'.1 (layoutsByPublicReading_total (S Z) c₀ m₀
    (((S Z).layoutsByPublicReading c₀ m₀).part (cAt Z hash, sevenAt Z hash), ⟨q.cm, q.rcd⟩))
  have hd : ZKCP.digestUnder hash ((S Z).layoutsByPublicReading c₀ m₀).encT
      (((S Z).layoutsByPublicReading c₀ m₀).part (cAt Z hash, sevenAt Z hash), ⟨q.cm, q.rcd⟩) = hash code := by
    unfold ZKCP.digestUnder
    rw [he]
    rfl
  rw [hd]
  obtain ⟨f, -, hp, hy⟩ := innerCompiledVerifier_formOf S f₀ Hb Z scope hash (hash code) prompt output q hS hq
  rw [hy]
  have ht : (S Z).typedOf (digToBytes (cAt Z hash)) f =
      (q.aux, ⟨q.cm, q.rcd⟩, ⟨q.copy, some q.piT, (q.cm', q.rcd', some q.piL), some q.piB⟩) := by
    unfold DescriptionDataAtFiles.typedOf
    rw [hp]
    rfl
  rw [ht]
  have hf := LPFD.Full.fitsD (S Z).A (S Z).E (S Z).G (S Z).DK (S Z).DP (S Z).runK (S Z).runP
    (S Z).dec (S Z).P (S Z).hStar (S Z).it (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL (asDescriptionFiles Z).lay (S Z).sR
    (S Z).hDK (S Z).hDP (S Z).hK (S Z).N (S Z).d₀ (c₀, m₀) (cAt Z hash, sevenAt Z hash) (hash code)
    prompt output
    (q.aux, ⟨q.cm, q.rcd⟩, ⟨q.copy, some q.piT, (q.cm', q.rcd', some q.piL), some q.piB⟩)
  refine (congrArg (fun v => DeterministicAlgorithm.evaluate hash v) hf).trans ?_
  exact innerCompiledVerifier_yes_of (((S Z).layoutsByPublicReading c₀ m₀).at (cAt Z hash, sevenAt Z hash)) hash (hash code)
    prompt output _ hb he rfl hv

end Johnson.Prover.Print
