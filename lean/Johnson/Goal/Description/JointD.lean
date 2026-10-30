-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/JointD.lean: the goal G8 at the built D*, from named hypotheses.
`G8_descriptionOfFields_of_remainingConditions`: at a family of `DescriptionDataAtFiles`. `G8_descriptionOfDataOnBytes`: at every record of letters.
`G8_theDescription`: at the name. The hypotheses: nine on numbers; the key file's, the entry file's
and the proof file's soundness; a claim with `meaning` and `carries`; `hext`: the extractor is the
told record's, then a map to weights; a bound and a ceiling on the error. `tie_tenth_oracle`,
`theDescription_tie`: printed here again, so that the tie and the goal stand in one file's print.
Limits. A conditional. At the name all but the three on soundness are paid (AtName.lean). The
theorem on codes is no hypothesis of this form: it sits beneath the three. No soundness of a
verifier that runs or ships is claimed.

-/
import Johnson.Flat.Told.Dec.LayoutsAtDescriptionOfFieldsO
import Johnson.Goal.Description.Description

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

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
open LPFD.Full (XF sBG sTG saltG KF)
open PV.EntryFive (dsF xsF)

attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF pub8

/-- **The goal G8 at the built D*, at every record of letters, from named hypotheses.** -/
theorem G8_descriptionOfDataOnBytes (L : DescriptionData) (c₀ : Digest) (m₀ : List (Dig 256))
    (φO : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → settingsAreValid s = true →
      (dataAtFiles L Z).A.Mat → Option (ModelWeights s))
    (ψ : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → settingsAreValid s = true →
      (dataAtFiles L Z).A.Mat → ModelWeights s)
    (eps : ℕ → ℕ → ℝ≥0∞)
    (ceil : ∀ t n, t ≤ queryBudget → n ≤ parserBudget → eps t n ≤ ceiling)
    (hk : ∀ Z, InScope Z = true → kThree .two (dataAtFiles L Z).DK [] (dataAtFiles L Z).DP ≤ KF (dataAtFiles L
                  Z).DK (dataAtFiles L Z).DP)
    (bL : ∀ Z, InScope Z = true → ∀ d ∈ dsF, (bsRound .two d.entry d.kind).b ≤ KF (dataAtFiles L Z).DK
        (dataAtFiles L Z).DP)
    (wLk : ∀ d ∈ dsF, d.entry.work ≤ 64) (own : ∀ d ∈ dsF, ∀ n ∈ d.opens, n < 2 ^ 16)
    (dL : ∀ d ∈ dsF, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (wK : ∀ Z, InScope Z = true → (dataAtFiles L Z).DK.workFit = true)
    (dK : ∀ Z, InScope Z = true → (dataAtFiles L Z).DK.depthFit = true)
    (wP : ∀ Z, InScope Z = true → (dataAtFiles L Z).DP.workFit = true)
    (dP : ∀ Z, InScope Z = true → (dataAtFiles L Z).DP.depthFit = true)
    (kS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles L Z).inputFieldsAtReadings c₀ m₀)))
    (eS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles L Z).inputFieldsAtReadings c₀ m₀)))
    (pS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles L Z).inputFieldsAtReadings c₀ m₀)))
    (claim : (Z : PublicFiles) → (dataAtFiles L Z).A.Mat → List Token → List Token → Prop)
    (meaning : ∀ Z, InScope Z = true → ∀ i (x' : List Token × List Token) a x,
      ((dataAtFiles L Z).inputFieldsAtReadings c₀ m₀).build x' a = some x → (∃ w, (soundnessAnalysisDataAtFullSize ((dataAtFiles L Z).inputFieldsAtReadings c₀
                                                 m₀)).Rno i x w) →
        claim Z i x'.1 x'.2)
    (carries : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → ∀ hr : readFiles Z = .ok pp,
      ∀ i prompt output, claim Z i prompt output →
        ∃ w, φO Z (settingsOfRead pp) (valid_of_read hr) i = some w ∧
          Policy.MeetsPolicy (settingsOfRead pp) pp.pol w prompt output)
    (hext : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → ∀ hr : readFiles Z = .ok pp,
      (dataAtFiles L Z).ext (settingsOfRead pp) = fun commitment queryLog =>
        (((dataAtFiles L Z).layoutsByPublicReading c₀ m₀).extractor commitment queryLog).bind (φO Z (settingsOfRead pp)
                                   (valid_of_read hr)))
    (bound : ∀ Z, InScope Z = true → ∀ t n,
      soundnessBoundOverTypedOracles ((dataAtFiles L Z).inputFieldsAtReadings c₀ m₀).W (soundnessAnalysisDataAtFullSize ((dataAtFiles L Z).inputFieldsAtReadings c₀ m₀)).εs (t + (8 + n)) 0
          + epsCode (t + (8 + n)) ≤ eps t n) :
    G8 (descriptionOfDataOnBytesIgnoringSecondHashArgument L) :=
  G8_descriptionOfFields_of_remainingConditions (dataAtFiles L) (committerAndProverWithParser (dataAtFiles L) L.honest decodeD L.f₀) c₀ m₀ φO ψ eps ceil hk bL wLk
      own dL wK dK wP dP kS eS pS claim meaning carries
    (fun Z _ _ _ => parseDec_honest (dataAtFiles L) L.honest decodeD L.f₀ Z) hext bound

/- Lean compares this name and does not open it: the statement below is G8_descriptionOfDataOnBytes's at L :=
  flashProveData, to the letter. -/
attribute [local irreducible] flashProveData

/-- **The goal G8 at the closed term, from the same hypotheses.** -/
theorem G8_theDescription (c₀ : Digest) (m₀ : List (Dig 256))
    (φO : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → settingsAreValid s = true →
      (dataAtFiles flashProveData Z).A.Mat → Option (ModelWeights s))
    (ψ : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → settingsAreValid s = true →
      (dataAtFiles flashProveData Z).A.Mat → ModelWeights s)
    (eps : ℕ → ℕ → ℝ≥0∞)
    (ceil : ∀ t n, t ≤ queryBudget → n ≤ parserBudget → eps t n ≤ ceiling)
    (hk : ∀ Z, InScope Z = true → kThree .two (dataAtFiles flashProveData Z).DK [] (dataAtFiles flashProveData Z).DP ≤ KF
        (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP)
    (bL : ∀ Z, InScope Z = true → ∀ d ∈ dsF, (bsRound .two d.entry d.kind).b ≤ KF (dataAtFiles flashProveData
        Z).DK (dataAtFiles flashProveData Z).DP)
    (wLk : ∀ d ∈ dsF, d.entry.work ≤ 64) (own : ∀ d ∈ dsF, ∀ n ∈ d.opens, n < 2 ^ 16)
    (dL : ∀ d ∈ dsF, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (wK : ∀ Z, InScope Z = true → (dataAtFiles flashProveData Z).DK.workFit = true)
    (dK : ∀ Z, InScope Z = true → (dataAtFiles flashProveData Z).DK.depthFit = true)
    (wP : ∀ Z, InScope Z = true → (dataAtFiles flashProveData Z).DP.workFit = true)
    (dP : ∀ Z, InScope Z = true → (dataAtFiles flashProveData Z).DP.depthFit = true)
    (kS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)))
    (eS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀
                                                     m₀)))
    (pS : ∀ Z, InScope Z = true → CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀
                                                     m₀)))
    (claim : (Z : PublicFiles) → (dataAtFiles flashProveData Z).A.Mat → List Token → List Token → Prop)
    (meaning : ∀ Z, InScope Z = true → ∀ i (x' : List Token × List Token) a x,
      ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).build x' a = some x → (∃ w, (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData
                                                         Z).inputFieldsAtReadings c₀ m₀)).Rno i x w) →
        claim Z i x'.1 x'.2)
    (carries : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → ∀ hr : readFiles Z = .ok pp,
      ∀ i prompt output, claim Z i prompt output →
        ∃ w, φO Z (settingsOfRead pp) (valid_of_read hr) i = some w ∧
          Policy.MeetsPolicy (settingsOfRead pp) pp.pol w prompt output)
    (hext : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → ∀ hr : readFiles Z = .ok pp,
      (dataAtFiles flashProveData Z).ext (settingsOfRead pp) = fun commitment queryLog =>
        (((dataAtFiles flashProveData Z).layoutsByPublicReading c₀ m₀).extractor commitment queryLog).bind (φO Z (settingsOfRead
                                           pp) (valid_of_read hr)))
    (bound : ∀ Z, InScope Z = true → ∀ t n,
      soundnessBoundOverTypedOracles ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)).εs (t +
                                                                                                                  (8 + n)) 0 + epsCode (t + (8 + n)) ≤ eps t n) :
    G8 theDescription := by
  obtain ⟨e, hc, hs⟩ := G8_descriptionOfDataOnBytes flashProveData c₀ m₀ φO ψ eps ceil hk bL wLk own dL wK dK wP dP kS eS
    pS claim meaning carries hext bound
  exact ⟨e, hc, ofBuilt (Q := fun D => SoundUnderPolicyAt D e) hs⟩

end FlashProve
