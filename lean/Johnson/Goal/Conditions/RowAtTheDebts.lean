-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/RowAtTheDebts.lean: THE ROW `top_SoundAndBinding` IN ITS FORM, AT THE ONE
CLOSED DESCRIPTION WITH THE TERMS LAID IN (`theBound K`, Johnson/Goal/Conditions/BindsAtThe.lean),
FROM ITS NAMED DEBTS, AT AN ERROR THAT IS NAMED IN BOTH HALVES. Statements and proofs. Nothing new
is shown: two files are joined.

Main names (namespace `FlashProve`).
  `soundUnderPolicyAt_theBound`: soundness under the files' policy of `theBound K` at the named
    error `epsFrame s theQueries`: the body of `G8_theBound`
    (Johnson/Goal/Conditions/SoundAtThe.lean), by the same call of
    `soundUnderPolicyAt_descriptionOfFields_withTerms` (Johnson/Goal/Conditions/ToldSoundTerms.lean), the error
      kept.
  **`nearestSoundAndBinding_theBound_debts`**: `NearestSoundAndBinding (theBound K)`
    (Ladder/Package.lean) at `joinError (epsFrame s theQueries) fun t => epsBind honestBudget (t +
    2)`.
  `nearestSoundOpened_theBound_debts`: `NearestSoundOpened (theBound K)` at twice that error.
NO "THERE IS" STANDS IN ANY CONCLUSION HERE, ON AN ERROR, A DESCRIPTION OR AN EXTRACTOR BUT THE ONE
INSIDE THE TOP STATEMENT `SoundAndBinding`, WHICH IS MET BY THE DESCRIPTION'S NAMED EXTRACTOR.

THE DEBTS, ALL.
- kS, eS, pS: the three hypotheses on soundness (`CompilerSoundnessConditionStatements.keySound`, `entrySound`, `proofSound`) at
  the description's own names, at every Z in scope WHERE `protocolDataWellFormed` SAYS YES.
- he: the named side's error of a round is at most c · 2^-a; has, hs, hc: a + s = 128, s ≤ 55,
  c ≤ 5/4: numbers.
- hE: `theCoding` is `codingCells`: an equation between two closed terms; it falls by rfl:
  `hE_the` (Johnson/Goal/Description/AtBound.lean).
LETTERS UNDER "FOR ALL": K (what of the honest side binding does not pin); ψ (a filler for an
auxiliary system's honest side: no statement reads it).

Limits. Those of the files named above. kS, eS AND pS ARE ALL OF SOUNDNESS; they are theorems
(keySound_holds, FlashProve.entrySound, proofSound_of_verify). `flashProveData`'s three decisions are
filled, its named side in part; its provers and honest side are still
unfilled (Johnson/Goal/Description/Lay.lean). Where `protocolDataWellFormed` says no the verifier refuses all. A
verifier that refuses everything meets the first clause for nothing: the statement weighs only
beside completeness of this very description. The nearest form speaks at the files whose policy is
exact match. `theBound K` is `VerifierAndGoals.theDescription` only if that name is laid so.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Goal.Conditions.RowAtThe
import Johnson.Goal.Conditions.SoundAtThe

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

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
  theProofData protocolDataWellFormed theDeadPlan theKeyGate theProofGate theLinkGate theProvers theNamed
  LPFD.Full.GF
  FlashProve.thePlan FlashProve.theItem

variable (K : TheCoins)

/-- **Soundness under the files' policy of the description, THE ERROR KEPT.** -/
theorem soundUnderPolicyAt_theBound
    (ψ : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → settingsAreValid s = true →
      (dataAtFiles flashProveData Z).A.Mat → ModelWeights s)
    (c : ℝ≥0∞) (a s : ℕ) (has : a + s = 128) (hc : c ≤ 1 + (4 : ℝ≥0∞)⁻¹)
    (he : ∀ Z, InScope Z = true → (dataAtFiles flashProveData Z).N.εs ≤ c * ((2 : ℝ≥0∞) ^ a)⁻¹)
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest []))) :
    SoundUnderPolicyAt (flashProveDescription.withTerms (theTerms K)) (epsFrame s theQueries) :=
  have e := entryFit_of_test entryFitB_dsFull_140
  soundUnderPolicyAt_descriptionOfFields_withTerms (dataAtFiles flashProveData)
    (committerAndProverWithParser (dataAtFiles flashProveData) flashProveData.honest decodeD flashProveData.f₀) allZeroDigest []
    phiThe backThe K.ri K.sl K.b₀ K.proveT K.Rand K.sample
    (fun Z => coinsAnchor Z (K.shape Z) (K.gen Z)) K.prove ψ (epsFrame s theQueries)
    (fun Z _ => (parts_the Z).hk) (fun Z _ => (parts_the Z).hE.bL) e.wLk e.own e.dL
    (fun Z _ => (parts_the Z).wK) (fun Z _ => (parts_the Z).dK) (fun Z _ => (parts_the Z).wP)
    (fun Z _ => (parts_the Z).dP)
    (fun Z h => keySound_theLay Z allZeroDigest [] (kS Z h))
    (fun Z h => entrySound_theLay Z allZeroDigest [] (eS Z h))
    (fun Z h => proofSound_theLay Z allZeroDigest [] (pS Z h)) claimThe (fun Z _ => meaning_the Z)
    (fun Z pp _ hr => carries_the Z pp hr)
    (fun Z _ _ _ => parseDec_honest (dataAtFiles flashProveData) flashProveData.honest decodeD flashProveData.f₀ Z)
    (fun Z h t n => errorBound_descriptionDataAtFiles (dataAtFiles flashProveData Z) allZeroDigest [] theQueries (fit_theLay Z) c a s has
      (he Z h) hc t n)

/-- **THE ROW's FORM AT THE DESCRIPTION, FROM ITS NAMED DEBTS, AT A NAMED ERROR.** -/
theorem nearestSoundAndBinding_theBound_debts
    (ψ : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → settingsAreValid s = true →
      (dataAtFiles flashProveData Z).A.Mat → ModelWeights s)
    (c : ℝ≥0∞) (a s : ℕ) (has : a + s = 128) (hc : c ≤ 1 + (4 : ℝ≥0∞)⁻¹)
    (he : ∀ Z, InScope Z = true → (dataAtFiles flashProveData Z).N.εs ≤ c * ((2 : ℝ≥0∞) ^ a)⁻¹)
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (hE : ∀ Zk, theCoding Zk = codingCells frS frZ 402653181 numsRef (ppAtFiles Zk.pol Zk.KL)
      Subtype.val) :
    NearestSoundAndBinding (theBound K)
      (joinError (epsFrame s theQueries) fun t => epsBind honestBudget (t + 2)) :=
  nearestSoundAndBinding_withTerms (fun _ => flashProveDescription) (fun _ => theTerms K) 8 2 (epsFrame s theQueries)
    (soundUnderPolicyAt_theBound K ψ c a s has hc he kS eS pS)
    fun Z pp _ h₂ => bindLaws_the K hE Z pp h₂

/-- Likewise `SoundOpened`, at twice that error. -/
theorem nearestSoundOpened_theBound_debts
    (ψ : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → settingsAreValid s = true →
      (dataAtFiles flashProveData Z).A.Mat → ModelWeights s)
    (c : ℝ≥0∞) (a s : ℕ) (has : a + s = 128) (hc : c ≤ 1 + (4 : ℝ≥0∞)⁻¹)
    (he : ∀ Z, InScope Z = true → (dataAtFiles flashProveData Z).N.εs ≤ c * ((2 : ℝ≥0∞) ^ a)⁻¹)
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings allZeroDigest [])))
    (hE : ∀ Zk, theCoding Zk = codingCells frS frZ 402653181 numsRef (ppAtFiles Zk.pol Zk.KL)
      Subtype.val) :
    NearestSoundOpened (theBound K) fun t =>
      2 * joinError (epsFrame s theQueries) (fun t => epsBind honestBudget (t + 2)) t :=
  nearestSoundOpened_of_at (theBound K) (epsFrame s theQueries) _
    (soundUnderPolicyAt_theBound K ψ c a s has hc he kS eS pS)
    (bindsAt_withTerms (theTerms K) 8 2 fun Z pp _ h₂ => bindLaws_the K hE Z pp h₂)

end FlashProve

#print axioms FlashProve.soundUnderPolicyAt_theBound
#print axioms FlashProve.nearestSoundAndBinding_theBound_debts
#print axioms FlashProve.nearestSoundOpened_theBound_debts
