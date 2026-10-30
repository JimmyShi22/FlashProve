-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Flat.Told.Dec.LayoutsAtDescriptionOfFieldsO
import VerifiableInference.ProbabilityGuards

/-! Johnson/Goal/SoundOr.lean: soundness under the files' policy at an error that is asked ONLY
WHERE IT IS BELOW 1.
  soundUnderPolicyAt_of_toldO_or   soundUnderPolicyAt_of_toldO (Johnson/PV/FitO.lean) with the
                                   premise «err ≤ eps ∨ 1 ≤ eps» for «err ≤ eps»: its proof to the
                                   letter but for the last line, which takes `Prob_le_one`
                                   (VerifiableInference/ProbabilityGuards.lean): a probability is at
                                   most 1.
  soundUnderPolicyAt_star          G8_descriptionOfFields_of_remainingConditions (Johnson/Flat/Told/Dec/LayoutsAtDescriptionOfFieldsO.lean) with
                                   `SoundUnderPolicyAt … eps` for `G8`, and that premise: the
                                   error's name is kept; `ceil` falls.
WHY. A closed error that stays finite (`VerifierAndGoals.soundnessErrorInQueries`) cannot lie above the compiler's bound at ALL
numbers of queries: the compiler's square term has the coefficient 50. Where the error is 1 or more
nothing is asked. Cut out of Johnson/Goal/TopOfRows.lean (its fifth text), names and statements
unturned: that file speaks of one description and is not in this library.
General in the family S and its side H. NO SOUNDNESS OF ANY VERIFIER: rules with premises. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Tie OnBytes.K.Arm.Pub
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open LPFD.Full (XF sBG sTG saltG KF)
open PV.EntryFive (dsF xsF)

attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF pub8

/-- soundUnderPolicyAt_of_toldO (Johnson/PV/FitO.lean), its proof to the letter but for the last
line: the bound is asked only where the error is below 1: a probability is at most 1. -/
theorem soundUnderPolicyAt_of_toldO_or (D : Description) (eps : ℕ → ℕ → ℝ≥0∞)
    (A : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ToldAtO D Z (settingsOfRead pp) (Policy.MeetsPolicy (settingsOfRead pp) pp.pol))
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      Parser.Within (D.parse Z) honestBudget)
    (hext : ∀ Z pp h₁ h₂, D.extractor Z (settingsOfRead pp) = (A Z pp h₁ h₂).extractor)
    (bound : ∀ Z pp h₁ h₂ t n, (A Z pp h₁ h₂).err t n ≤ eps t n ∨ 1 ≤ eps t n) :
    SoundUnderPolicyAt D eps := by
  intro Z pp h₁ h₂
  refine ⟨ownParser Z pp h₁ h₂, ?_⟩
  intro Form prove parse n hn
  have key := soundForWith_system_of_toldO D Z (A Z pp h₁ h₂).c₀ (A Z pp h₁ h₂).m₀
    (A Z pp h₁ h₂).T (settingsOfRead pp) (A Z pp h₁ h₂).pair (A Z pp h₁ h₂).fits
    (A Z pp h₁ h₂).claim (A Z pp h₁ h₂).Wn (A Z pp h₁ h₂).Rno (A Z pp h₁ h₂).x₀
    (A Z pp h₁ h₂).εs (A Z pp h₁ h₂).core (A Z pp h₁ h₂).meaning
    (A Z pp h₁ h₂).noCoin (A Z pp h₁ h₂).asks (A Z pp h₁ h₂).once
    (A Z pp h₁ h₂).spare (A Z pp h₁ h₂).word (A Z pp h₁ h₂).code
    (A Z pp h₁ h₂).reads (A Z pp h₁ h₂).q₀ (A Z pp h₁ h₂).hq₀ (A Z pp h₁ h₂).φ (A Z pp h₁ h₂).ψ
    (Policy.MeetsPolicy (settingsOfRead pp) pp.pol) (A Z pp h₁ h₂).carries (hext Z pp h₁ h₂)
    Form prove parse n hn
  intro cq pq St c hc p hp
  rcases bound Z pp h₁ h₂ (cq + pq) n with hb | hb
  · exact le_trans (key cq pq St c hc p hp) hb
  · exact le_trans (Prob_le_one _ _) hb

section
variable (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (H : CommitterProverFormAndParser fun Z => (S Z).toDescriptionFields) (c₀ : Digest)
  (m₀ : List (Dig 256))

/-- G8_descriptionOfFields_of_remainingConditions (Johnson/Flat/Told/Dec/LayoutsAtDescriptionOfFieldsO.lean), with `SoundUnderPolicyAt … eps` for `G8`. -/
theorem soundUnderPolicyAt_star
    (φO : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → settingsAreValid s = true →
      (S Z).A.Mat → Option (ModelWeights s))
    (ψ : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → settingsAreValid s = true →
      (S Z).A.Mat → ModelWeights s)
    (eps : ℕ → ℕ → ℝ≥0∞)
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
        (((S Z).layoutsByPublicReading c₀ m₀).extractor commitment queryLog).bind
          (φO Z (settingsOfRead pp) (valid_of_read hr)))
    (bound : ∀ Z, InScope Z = true → ∀ t n,
      soundnessBoundOverTypedOracles ((S Z).inputFieldsAtReadings c₀ m₀).W (soundnessAnalysisDataAtFullSize ((S Z).inputFieldsAtReadings c₀ m₀)).εs (t + (8 + n)) 0 +
        epsCode (t + (8 + n)) ≤ eps t n ∨ 1 ≤ eps t n) :
    SoundUnderPolicyAt (descriptionOfFields (fun Z => (S Z).toDescriptionFields) H) eps :=
  soundUnderPolicyAt_of_toldO_or (descriptionOfFields (fun Z => (S Z).toDescriptionFields) H) eps
    (fun Z pp h₁ h₂ => publicReadingFitAtDescriptionOfFields S H c₀ m₀ Z (settingsOfRead pp) _ (claim Z) _ _ _ _
      (φO Z (settingsOfRead pp) (valid_of_read h₂)) (ψ Z (settingsOfRead pp) (valid_of_read h₂))
      (fun d => compilerSoundnessConditions_layoutsByPublicReading (S Z) c₀ m₀ (hk Z h₁) (bL Z h₁) wLk own dL (wK Z h₁) (dK Z h₁) (wP Z h₁)
        (dP Z h₁) (kS Z h₁) (eS Z h₁) (pS Z h₁) d)
      (meaning Z h₁) (carries Z pp h₁ h₂))
    ownParser
    (fun Z pp h₁ h₂ => hext Z pp h₁ h₂)
    fun Z _ h₁ _ t n => bound Z h₁ t n

end

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.soundUnderPolicyAt_of_toldO_or
#print axioms VerifierAndGoals.AtTheName.soundUnderPolicyAt_star
