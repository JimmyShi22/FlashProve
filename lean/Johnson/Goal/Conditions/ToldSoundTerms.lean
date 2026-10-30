-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/ToldSoundTerms.lean: **the goal G8 at D⋆ with the honest side's terms laid
  in, without the debt hext**: at `(descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).withTerms (honestTermsAtDescriptionOfFields …)`
  (Johnson/Goal/Conditions/DescribeTerms.lean | BindsAtDescriptionOfFields.lean) the extractor is, by definition,
  the told record's, then φ: so what G8_descriptionOfFields_of_remainingConditions (Johnson/Flat/Told/Dec/LayoutsAtDescriptionOfFieldsO.lean)
  asks as hext of (S Z).ext holds there by rfl, whatever (S Z).ext is.
Why. A text not here lays VerifierAndGoals.theDescription := fun _ => (descriptionOfDataOnBytes flashProveDataNoExtractor).withTerms theTerms,
  flashProveDataNoExtractor's own ext a place-holder that finds nothing. The bridge soundUnderPolicyAt_withTerms
  (Johnson/Goal/Conditions/DescribeTermsSound.lean) asks hext of D's own extractor: at such a
  flashProveDataNoExtractor that equation fails wherever the told record's extractor finds an index to which φ gives
  weights: it is not to be had there. Here soundness is shown of the description with the terms
  directly.
  ToldAtO.withTerms B Q                 general in D: all that the fit asks at one Z (ToldAtO,
    Johnson/PV/FitO.lean) passes from D to D.withTerms Q, field by field: input · F · P · More ·
    readMore are D's by rfl
  soundUnderPolicyAt_withTerms_of_told  general in D: SoundUnderPolicyAt (D.withTerms Q) eps from
    ToldAtO at D, where Q's record and φ are the ToldAtO's (hQ: an equation between two functions;
    at honestTermsAtDescriptionOfFields: rfl)
  **soundUnderPolicyAt_descriptionOfFields_withTerms** at honestTermsAtDescriptionOfFields: it is the premise «sound» of
    nearestSoundAndBinding_descriptionOfFields, as that lies
  **G8_descriptionOfFields_withTerms**                 the stored G8 there
The named debts, all: G8_descriptionOfFields_of_remainingConditions's without hext: eps with ceil · bound · hk (at «[]») · bL · wLk ·
  own · dL · wK dK wP dP · kS · eS · pS · claim with meaning · carries (at φ Z (settingsOfRead pp))
  · ownParser. Riding in S: hDK hDP hK; in N: hε.
Who reads each letter. φ: the extractor (by withTerms) and carries. ψ: a total filler for an
  auxiliary system's honest side: no statement reads it. back ri sl b₀ proveT Rand sample coins
  prove: the honest side alone: soundness reads none. (S Z).ext: nobody: withTerms overwrites it. c₀
  m₀: the pair at which the record's input is taken.
∃: meaning's «∃ w, Rno i x w» in a premise of a premise; carries' «∃ w, φ … i = some w ∧ …»: w is
  φ's own value: nothing is chosen.
Does not show. A conditional: keySound · entrySound · proofSound · the meaning · carries are shown
  at no letters; no S is built. A theorem on (…).withTerms … is a theorem on that description (the
  goals' verifier is D's: verify_withTerms := rfl). The silly members: as in LayoutsAtDescriptionOfFieldsO.lean's head: at
  «yes to all» the premises on soundness fail (for a protocol that accepts all: YesToAll.lean [not in this library]; at
  the frame: by argument alone); at «no to all» the conclusion is true and empty.
No soundness is claimed.
-/
import Johnson.Flat.Told.Dec.LayoutsAtDescriptionOfFieldsO
import Johnson.Goal.Conditions.BindsAtDescriptionOfFields

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles

/-- **All that the fit asks at one Z passes to the description with the terms laid in.** -/
def ToldAtO.withTerms {D : Description} {Z : PublicFiles} {s : IntegerTransformer.Settings}
    {newClaim : ModelWeights s → List Token → List Token → Prop} (B : ToldAtO D Z s newClaim)
    (Q : HonestTerms D) : ToldAtO (D.withTerms Q) Z s newClaim where
  c₀ := B.c₀
  m₀ := B.m₀
  T := B.T
  pair := B.pair
  claim := B.claim
  Wn := B.Wn
  Rno := B.Rno
  x₀ := B.x₀
  εs := B.εs
  q₀ := B.q₀
  φ := B.φ
  ψ := B.ψ
  fits := B.fits
  core := B.core
  meaning := B.meaning
  noCoin := B.noCoin
  asks := B.asks
  once := B.once
  spare := B.spare
  word := B.word
  code := B.code
  reads := B.reads
  hq₀ := B.hq₀
  carries := B.carries

/-- **Soundness under the files' policy OF THE DESCRIPTION WITH THE TERMS, from the fit AT D.** D's own extractor is not read. -/
theorem soundUnderPolicyAt_withTerms_of_told (D : Description) (Q : HonestTerms D) (eps : ℕ → ℕ → ℝ≥0∞)
    (A : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ToldAtO D Z (settingsOfRead pp) (Policy.MeetsPolicy (settingsOfRead pp) pp.pol))
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      Parser.Within (D.parse Z) honestBudget)
    (hQ : ∀ Z pp h₁ h₂, (fun commitment queryLog =>
      ((Q.T Z).extractor commitment queryLog).bind (Q.φ Z (settingsOfRead pp))) = (A Z pp h₁ h₂).extractor)
    (bound : ∀ Z pp h₁ h₂ t n, (A Z pp h₁ h₂).err t n ≤ eps t n) :
    SoundUnderPolicyAt (D.withTerms Q) eps :=
  soundUnderPolicyAt_of_toldO (D.withTerms Q) eps (fun Z pp h₁ h₂ => (A Z pp h₁ h₂).withTerms Q) ownParser hQ
    bound

end VerifierAndGoals.Fit

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

variable (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (H : CommitterProverFormAndParser fun Z => (S Z).toDescriptionFields) (c₀ : Digest)
  (m₀ : List (Dig 256))

variable
  (φ : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → ((descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).input Z c₀ m₀).Index →
    Option (ModelWeights s))
  (back : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → ModelWeights s → ((descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).input Z c₀ m₀).Index)
  (ri : (Z : PublicFiles) → _root_.Iop.Enum ((descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).input Z c₀ m₀).protocol.EncodingRandomness)
  (sl : PublicFiles → _root_.Iop.Enum (ℕ → Rom.Bits)) (b₀ : (Z : PublicFiles) → ((descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).input Z c₀ m₀).LeafBody)
  (proveT : (Z : PublicFiles) → ((descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).input Z c₀ m₀).Index × ((descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).input Z c₀ m₀).protocol.EncodingRandomness × (ℕ → Rom.Bits) →
    (l : List (((descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).input Z c₀ m₀).Instance × Unit)) →
    Rom.OComp (rom 256) (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 ((descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).input Z c₀ m₀).protocol
      ((descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).input Z c₀ m₀).offlineRoundSplits ((descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).input Z c₀ m₀).linkRoundSplits) l))
  (Rand : Type) (sample : RandomizedAlgorithm Rand)
  (coins : (Z : PublicFiles) → Rand → DeterministicAlgorithm (Fin (((descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).input Z c₀ m₀).coinBound + 1)))
  (prove : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → RandomizedAlgorithm H.Form)


/-- **SOUNDNESS UNDER THE FILES' POLICY AT D⋆ WITH THE TERMS LAID IN: NO hext.** -/
theorem soundUnderPolicyAt_descriptionOfFields_withTerms
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
    (carries : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ∀ i prompt output, claim Z i prompt output →
        ∃ w, φ Z (settingsOfRead pp) i = some w ∧
          Policy.MeetsPolicy (settingsOfRead pp) pp.pol w prompt output)
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      Parser.Within ((descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).parse Z) honestBudget)
    (bound : ∀ Z, InScope Z = true → ∀ t n,
      soundnessBoundOverTypedOracles ((S Z).inputFieldsAtReadings c₀ m₀).W (soundnessAnalysisDataAtFullSize ((S Z).inputFieldsAtReadings c₀ m₀)).εs (t + (8 + n)) 0 + epsCode (t + (8 + n)) ≤ eps t n) :
    SoundUnderPolicyAt ((descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).withTerms (honestTermsAtDescriptionOfFields S H c₀ m₀ φ back ri sl b₀ proveT Rand sample coins prove)) eps :=
  soundUnderPolicyAt_withTerms_of_told (descriptionOfFields (fun Z => (S Z).toDescriptionFields) H) (honestTermsAtDescriptionOfFields S H c₀ m₀ φ back ri sl b₀ proveT Rand sample coins prove) eps
    (fun Z pp h₁ h₂ => publicReadingFitAtDescriptionOfFields S H c₀ m₀ Z (settingsOfRead pp) _ (claim Z) _ _ _ _
      (φ Z (settingsOfRead pp)) (ψ Z (settingsOfRead pp) (valid_of_read h₂))
      (fun d => compilerSoundnessConditions_layoutsByPublicReading (S Z) c₀ m₀ (hk Z h₁) (bL Z h₁) wLk own dL (wK Z h₁) (dK Z h₁) (wP Z h₁) (dP Z h₁) (kS Z h₁) (eS Z h₁) (pS Z h₁) d)
      (meaning Z h₁) (carries Z pp h₁ h₂))
    ownParser
    (fun _ _ _ _ => rfl)
    fun Z _ h₁ _ t n => bound Z h₁ t n

/-- **THE STORED G8 AT D⋆ WITH THE TERMS LAID IN: G8_descriptionOfFields_of_remainingConditions's DEBTS WITHOUT hext.** -/
theorem G8_descriptionOfFields_withTerms
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
    (carries : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ∀ i prompt output, claim Z i prompt output →
        ∃ w, φ Z (settingsOfRead pp) i = some w ∧
          Policy.MeetsPolicy (settingsOfRead pp) pp.pol w prompt output)
    (ownParser : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      Parser.Within ((descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).parse Z) honestBudget)
    (bound : ∀ Z, InScope Z = true → ∀ t n,
      soundnessBoundOverTypedOracles ((S Z).inputFieldsAtReadings c₀ m₀).W (soundnessAnalysisDataAtFullSize ((S Z).inputFieldsAtReadings c₀ m₀)).εs (t + (8 + n)) 0 + epsCode (t + (8 + n)) ≤ eps t n) :
    G8 fun _ => (descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).withTerms (honestTermsAtDescriptionOfFields S H c₀ m₀ φ back ri sl b₀ proveT Rand sample coins prove) :=
  ⟨eps, ceil, soundUnderPolicyAt_descriptionOfFields_withTerms S H c₀ m₀ φ back ri sl b₀ proveT Rand sample coins prove ψ eps hk bL wLk
    own dL wK dK wP dP kS eS pS claim meaning carries ownParser bound⟩

end FlashProve

#print axioms VerifierAndGoals.Fit.ToldAtO.withTerms
#print axioms VerifierAndGoals.Fit.soundUnderPolicyAt_withTerms_of_told
#print axioms FlashProve.soundUnderPolicyAt_descriptionOfFields_withTerms
#print axioms FlashProve.G8_descriptionOfFields_withTerms
