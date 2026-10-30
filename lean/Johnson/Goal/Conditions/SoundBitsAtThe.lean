-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/SoundBitsAtThe.lean: **G8bits (Ladder/Bits.lean:174: soundness under the
  files' policy at the error soundnessErrorInQueries, with the verifier's own queries within verifierQueryAllowance) at the term
  theBound K** (Johnson/Goal/Conditions/BindsAtThe.lean), as a reduction to the three hypotheses on
  soundness and one inequality on the named εs.
  soundUnderPolicyAt_withTerms_of_told_or   general in D: soundUnderPolicyAt_withTerms_of_told
    (ToldSoundTerms.lean) with the bound asked only where the error is below 1 (the rule
    soundUnderPolicyAt_of_toldO_or, Johnson/Goal/SoundOr.lean)
  **soundUnderPolicyAt_bits_theBound**      SoundUnderPolicyAt (theBound K o) soundnessErrorInQueries
  **G8bits_theBound**                       G8bits (theBound K), at every K
The debts, all: kS · eS · pS: keySound · entrySound · proofSound at the named side, at every Z in
  scope where protocolDataWellFormed says yes · he2: the named side's εs ≤ 2 / 2^128. Nothing else.
How. The error: frame_le_bits (Ladder/BitsOfStep.lean: a round's error of at most 2 / 2^128 and a
  count of at most 2^23 - 9 give soundnessErrorInQueries, where soundnessErrorInQueries < 1) at the count of verifierQueryCountBound_descriptionDataAtFiles (ToldBound.lean)
  with fit_theLay (NumbersAtThe.lean); where soundnessErrorInQueries ≥ 1: a probability is at most 1. The extractor: by
  withTerms (ToldAtO.withTerms). meaning | carries: SoundAtThe.lean. VerifierWithin:
  WithinAtThe.lean.
Who reads each letter. K: the honest side alone. o: nobody (theBound K does not read it). ∃: none
  but those of SoundAtThe.lean's claimThe | carries_the and VerifierWithin's two numerals.
Does not show. A reduction: no goal is proved here.
  The three are hypotheses here, asked at a named εs of at most 2 / 2^128. Where they are proved,
  and how far: the head of Johnson/Goal/TopOfThree.lean, limits (1), (3) and (4): that number is a
  letter there, no price. Where protocolDataWellFormed says no the verifier refuses all. All limits of
  SoundAtThe.lean's and Ladder/Bits.lean's heads stand.



No soundness is claimed.
-/
import Johnson.Goal.Conditions.SoundAtThe
import Johnson.Goal.Conditions.WithinAtThe
import Johnson.Goal.SoundOr
import Ladder.BitsOfStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles

/-- **Soundness under the files' policy of the description with the terms, from the fit at D; the bound is asked only where the error is below 1.** -/
theorem soundUnderPolicyAt_withTerms_of_told_or (D : Description) (Q : HonestTerms D) (eps : ℕ → ℕ → ℝ≥0∞)
    (A : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ToldAtO D Z (settingsOfRead pp) (Policy.MeetsPolicy (settingsOfRead pp) pp.pol))
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      Parser.Within (D.parse Z) honestBudget)
    (hQ : ∀ Z pp h₁ h₂, (fun commitment queryLog =>
      ((Q.T Z).extractor commitment queryLog).bind (Q.φ Z (settingsOfRead pp))) = (A Z pp h₁ h₂).extractor)
    (bound : ∀ Z pp h₁ h₂ t n, (A Z pp h₁ h₂).err t n ≤ eps t n ∨ 1 ≤ eps t n) :
    SoundUnderPolicyAt (D.withTerms Q) eps :=
  VerifierAndGoals.AtTheName.soundUnderPolicyAt_of_toldO_or (D.withTerms Q) eps (fun Z pp h₁ h₂ => (A Z pp h₁ h₂).withTerms Q)
    ownParser hQ bound

end VerifierAndGoals.Fit

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Tie OnBytes.K.Arm.Pub
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open LPFD.Full (XF GF sBG sTG saltG KF)
open PV.EntryFive (dsF xsF)

/- Lean compares these names and does not unfold them. -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF pub8 theCoding theKeyData
  theProofData protocolDataWellFormed theDeadPlan theKeyGate theProofGate theLinkGate theProvers theNamed LPFD.Full.GF
  FlashProve.thePlan FlashProve.theItem

variable (K : TheCoins)

/-- **Soundness under the files' policy at the error soundnessErrorInQueries, at the term with the terms laid in.** -/
theorem soundUnderPolicyAt_bits_theBound (o : SecondHashFunctionType)
    (he2 : ∀ Z, InScope Z = true → (dataAtFiles flashProveData Z).N.εs ≤ 2 * ((2 : ℝ≥0∞) ^ 128)⁻¹)
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))) :
    SoundUnderPolicyAt (theBound K o) soundnessErrorInQueries :=
  have e := entryFit_of_test entryFitB_dsFull_140
  soundUnderPolicyAt_withTerms_of_told_or flashProveDescription (theTerms K) soundnessErrorInQueries
    (fun Z pp h₁ h₂ => publicReadingFitAtDescriptionOfFields (dataAtFiles flashProveData) (committerAndProverWithParser (dataAtFiles flashProveData) flashProveData.honest decodeD flashProveData.f₀)
      allZeroDigest [] Z (settingsOfRead pp) _ (claimThe Z) _ _ _ _ (phiThe Z (settingsOfRead pp))
      (fun M => VerifiableInference.OnPublicFiles.phiAt (valid_of_read h₂) M)
      (fun d => compilerSoundnessConditions_layoutsByPublicReading (dataAtFiles flashProveData Z) allZeroDigest [] (parts_the Z).hk (parts_the Z).hE.bL e.wLk e.own e.dL
        (parts_the Z).wK (parts_the Z).dK (parts_the Z).wP (parts_the Z).dP
        (keySound_theLay Z allZeroDigest [] (kS Z h₁)) (entrySound_theLay Z allZeroDigest [] (eS Z h₁))
        (proofSound_theLay Z allZeroDigest [] (pS Z h₁)) d)
      (meaning_the Z) (carries_the Z pp h₂))
    (fun Z _ _ _ => parseDec_honest (dataAtFiles flashProveData) flashProveData.honest decodeD flashProveData.f₀ Z)
    (fun _ _ _ _ => rfl)
    fun Z _ h₁ _ t n => (lt_or_ge (soundnessErrorInQueries t n) 1).imp
      (fun hb => frame_le_bits _ t n _ (he2 Z h₁)
        (le_trans (Nat.add_le_add_right (verifierQueryCountBound_descriptionDataAtFiles (dataAtFiles flashProveData Z) allZeroDigest [] theQueries (fit_theLay Z)) 9)
          (by unfold theQueries; norm_num)) hb) id

/-- **G8bits AT THE TERM, AT EVERY K: FROM THE THREE HYPOTHESES ON SOUNDNESS WHERE THE TEST SAYS YES, AND εs ≤ 2 / 2^128.** -/
theorem G8bits_theBound
    (he2 : ∀ Z, InScope Z = true → (dataAtFiles flashProveData Z).N.εs ≤ 2 * ((2 : ℝ≥0∞) ^ 128)⁻¹)
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))) :
    G8bits (theBound K) :=
  ⟨verifierWithin_theBound K _, soundUnderPolicyAt_bits_theBound K _ he2 kS eS pS⟩

end FlashProve

#print axioms VerifierAndGoals.Fit.soundUnderPolicyAt_withTerms_of_told_or
#print axioms FlashProve.soundUnderPolicyAt_bits_theBound
#print axioms FlashProve.G8bits_theBound
