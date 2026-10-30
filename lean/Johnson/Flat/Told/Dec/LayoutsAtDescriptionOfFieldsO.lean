-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Told/Dec/LayoutsAtDescriptionOfFieldsO.lean: a twin, made by program, of a file that is not in this library,
  over DescriptionDataAtFiles (Johnson/Goal/Tie/DescriptionOnDecodedProof.lean) | DescriptionFields | descriptionOfFields (DescribeT.lean)
  (DescriptionDataAtFiles has the field dec behind runP; its types are the D-names at dsF
  xsF dec) and Johnson/Flat/Told/Dec/TAtLaws.lean.
The original is not in this library; the declared names are the original's. Where this twin
  parts: G8_descriptionOfFields_of_remainingConditions has entrySound (eS, at every Z in scope) in the theorem on codes'
  place, hk at «[]», bL at every Z in scope, and wLk own dL on dsF's numbers. Limits: G8_descriptionOfFields_of_remainingConditions
  is a conditional: keySound, entrySound, proofSound, the meaning, carries and hext are premises.
This variant: DescriptionDataAtFiles has a field G : FilesParameters XF RecFull: «S.G» stands where a variant that is not
  in this library has «(GF Zk)»; nothing else parts.
No soundness is claimed. Limits: lean/LIMITS.md, L57.
-/
import Johnson.Flat.Told.Dec.LayoutsAtDescriptionOfFields
import Johnson.PV.FitO

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ENNReal

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Tie OnBytes.K.Arm.Pub
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open LPFD.Full (XF sBG sTG saltG KF)
open PV.EntryFive (dsF xsF)

/- Lean compares these names and does not unfold them. -/
attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF pub8

variable (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (H : CommitterProverFormAndParser fun Z => (S Z).toDescriptionFields) (c₀ : Digest) (m₀ : List (Dig 256))

/-- (4) **ToldAtO AT D⋆**, from three premises: the fifteen at every d, the meaning, and that φ carries the claim. -/
def publicReadingFitAtDescriptionOfFields (Z : PublicFiles) (s : IntegerTransformer.Settings)
    (newClaim : ModelWeights s → List Token → List Token → Prop)
    (claim : (S Z).A.Mat → List Token → List Token → Prop) (Wn : Type)
    (Rno : (S Z).A.Mat → XF → Wn → Prop) (x₀ : XF) (εs : ℝ≥0∞)
    (φ : (S Z).A.Mat → Option (ModelWeights s)) (ψ : (S Z).A.Mat → ModelWeights s)
    (core : ∀ d, CompilerSoundnessConditions ((layoutsByPublicReadingAtDescriptionOfFields S H c₀ m₀ Z).beside Wn Rno x₀ εs d))
    (meaning : ∀ i (x' : List Token × List Token) a x, ((S Z).inputFieldsAtReadings c₀ m₀).build x' a = some x →
      (∃ w, Rno i x w) → claim i x'.1 x'.2)
    (carries : ∀ i prompt output, claim i prompt output → ∃ w, φ i = some w ∧ newClaim w prompt output) :
    ToldAtO (descriptionOfFields (fun Z => (S Z).toDescriptionFields) H) Z s newClaim where
  c₀ := c₀
  m₀ := m₀
  T := layoutsByPublicReadingAtDescriptionOfFields S H c₀ m₀ Z
  pair := Prod.mk
  claim := claim
  Wn := Wn
  Rno := Rno
  x₀ := x₀
  εs := εs
  q₀ := 8
  φ := φ
  ψ := ψ
  fits := fits_descriptionOfFields S H c₀ m₀ Z
  core := core
  meaning := meaning
  noCoin := layoutsByPublicReading_noCoin (S Z) c₀ m₀
  asks := layoutsByPublicReading_asks (S Z) c₀ m₀
  once := layoutsByPublicReading_once (S Z) c₀ m₀
  spare := layoutsByPublicReading_spare (S Z) c₀ m₀
  word := layoutsByPublicReading_word (S Z) c₀ m₀
  code := layoutsByPublicReading_code (S Z) c₀ m₀
  reads := reads_descriptionOfFields S H c₀ m₀ Z
  hq₀ := readingsQueryBound_descriptionOfFields S H c₀ m₀ Z
  carries := carries

/-- **G8 (Ladder.lean) AT D⋆, FROM NAMED HYPOTHESES.** -/
theorem G8_descriptionOfFields_of_remainingConditions
    (φO : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → settingsAreValid s = true →
      (S Z).A.Mat → Option (ModelWeights s))
    (ψ : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → settingsAreValid s = true →
      (S Z).A.Mat → ModelWeights s)
    (eps : ℕ → ℕ → ℝ≥0∞)
    (ceil : ∀ t n, t ≤ queryBudget → n ≤ parserBudget → eps t n ≤ ceiling)
    (hk : ∀ Z, InScope Z = true → kThree .two (S Z).DK [] (S Z).DP ≤ KF (S Z).DK (S Z).DP)
    (bL : ∀ Z, InScope Z = true → ∀ d ∈ dsF, (bsRound .two d.entry d.kind).b ≤ KF (S Z).DK (S Z).DP)
    (wLk : ∀ d ∈ dsF, d.entry.work ≤ 64) (own : ∀ d ∈ dsF, ∀ n ∈ d.opens, n < 2 ^ 16)
    (dL : ∀ d ∈ dsF, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (wK : ∀ Z, InScope Z = true → (S Z).DK.workFit = true)
    (dK : ∀ Z, InScope Z = true → (S Z).DK.depthFit = true)
    (wP : ∀ Z, InScope Z = true → (S Z).DP.workFit = true)
    (dP : ∀ Z, InScope Z = true → (S Z).DP.depthFit = true)
    (kS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((S Z).inputFieldsAtReadings c₀ m₀)))
    (eS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((S Z).inputFieldsAtReadings c₀ m₀)))
    (pS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((S Z).inputFieldsAtReadings c₀ m₀)))
    (claim : (Z : PublicFiles) → (S Z).A.Mat → List Token → List Token → Prop)
    (meaning : ∀ Z, InScope Z = true → ∀ i (x' : List Token × List Token) a x,
      ((S Z).inputFieldsAtReadings c₀ m₀).build x' a = some x → (∃ w, (soundnessAnalysisDataAtFullSize ((S Z).inputFieldsAtReadings c₀ m₀)).Rno i x w) →
        claim Z i x'.1 x'.2)
    (carries : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → ∀ hr : readFiles Z = .ok pp,
      ∀ i prompt output, claim Z i prompt output →
        ∃ w, φO Z (settingsOfRead pp) (valid_of_read hr) i = some w ∧
          Policy.MeetsPolicy (settingsOfRead pp) pp.pol w prompt output)
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      Parser.Within ((descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).parse Z) honestBudget)
    (hext : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → ∀ hr : readFiles Z = .ok pp,
      (S Z).ext (settingsOfRead pp) = fun commitment queryLog =>
        (((S Z).layoutsByPublicReading c₀ m₀).extractor commitment queryLog).bind (φO Z (settingsOfRead pp) (valid_of_read hr)))
    (bound : ∀ Z, InScope Z = true → ∀ t n,
      soundnessBoundOverTypedOracles ((S Z).inputFieldsAtReadings c₀ m₀).W (soundnessAnalysisDataAtFullSize ((S Z).inputFieldsAtReadings c₀ m₀)).εs (t + (8 + n)) 0 + epsCode (t + (8 + n)) ≤ eps t n) :
    G8 fun _ => (descriptionOfFields (fun Z => (S Z).toDescriptionFields) H) :=
  G8_of_toldO (fun _ => (descriptionOfFields (fun Z => (S Z).toDescriptionFields) H)) eps ceil
    (fun Z pp h₁ h₂ => publicReadingFitAtDescriptionOfFields S H c₀ m₀ Z (settingsOfRead pp) _ (claim Z) _ _ _ _
      (φO Z (settingsOfRead pp) (valid_of_read h₂)) (ψ Z (settingsOfRead pp) (valid_of_read h₂))
      (fun d => compilerSoundnessConditions_layoutsByPublicReading (S Z) c₀ m₀ (hk Z h₁) (bL Z h₁) wLk own dL (wK Z h₁) (dK Z h₁) (wP Z h₁) (dP Z h₁) (kS Z h₁) (eS Z h₁) (pS Z h₁) d)
      (meaning Z h₁) (carries Z pp h₁ h₂))
    ownParser
    (fun Z pp h₁ h₂ => hext Z pp h₁ h₂)
    fun Z _ h₁ _ t n => bound Z h₁ t n

end FlashProve

#print axioms FlashProve.publicReadingFitAtDescriptionOfFields
#print axioms FlashProve.G8_descriptionOfFields_of_remainingConditions
