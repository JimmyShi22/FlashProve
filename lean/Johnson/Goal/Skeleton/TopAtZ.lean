-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/TopAtZ.lean: THE TOP ON SOUNDNESS AT ONE SET OF PUBLIC FILES Z, from the two
hypotheses AT THAT Z ALONE.

Why. `KeySound` and `ProofSound` (Johnson/Goal/Conditions/RowsAtTheRecord.lean) are closed under
"for all Z in scope at which `protocolDataWellFormed` accepts". One Z at which a hypothesis fails makes the whole
premise false, and then `top_sound_of_two` (Johnson/Goal/TopOfTwo.lean) says nothing, not even at
the release's own files. But the chain beneath it spends its hypotheses Z by Z. Here each layer of
that chain is stated at one Z. NO NEW MATHEMATICS: each proof is its pair's own text with "for all
Z" taken off the front. The forms with "for all Z" stand beside these.

Main names (namespace `VerifierAndGoals.AtTheName`).
  `SoundUnderPolicyAtZ D eps Z pp`: the body of `SoundUnderPolicyAt D eps` (Ladder.lean) at Z, pp.
    `soundUnderPolicyAt_iff_atZ`: `SoundUnderPolicyAt D eps` is that body at all Z in scope that are
    read: by definition.
  `KeySoundAt Z`, `ProofSoundAt Z`: the bodies of `KeySound` and `ProofSound` at Z, each behind
    "`protocolDataWellFormed (asDescriptionFiles Z) = true` →". `keySound_iff_at`, `proofSound_iff_at`: by definition.
  The layers, each with its pair:
    `soundUnderPolicyAtZ_of_toldO_or`   `soundUnderPolicyAt_of_toldO_or` (Johnson/Goal/SoundOr.lean)
    `soundUnderPolicyAtZ_star`          `soundUnderPolicyAt_star` (the same file)
    `soundUnderPolicyAtZ_numbers`       `soundUnderPolicyAt_numbers` (Johnson/Goal/TopOfThree.lean)
    `soundUnderPolicyAtZ_of_two`        `soundUnderPolicyAt_bits`, `…_of_three`, `…_of_two`
    `sound_of_atZ`                      `soundAt_of_soundUnderPolicyAt` (Ladder/Ties.lean)
  **`sound_at`**: at Z in scope, read, with exact match: from `KeySoundAt Z` and `ProofSoundAt Z`:
    `Sound` of the name's system of record at Z, at fun t => `VerifierAndGoals.soundnessErrorInQueries` t 1: THE BODY OF
    `NearestSound theDescription fun t => VerifierAndGoals.soundnessErrorInQueries t 1` (Ladder/Package.lean) AT Z.
  `proofSound_at_of_proofFileAt`: `ProofFileAt Z` (Johnson/Goal/Skeleton/ProofFile.lean) gives
    `CompilerSoundnessConditionStatements.proofSound (bZ Z)` where `protocolDataWellFormed` accepts: `proofSound_of_proofFileAt`'s proof at Z.
  `top_sound_of_at`: the form with "for all Z" back from `sound_at`: nothing is lost.

Limits. `KeySoundAt Z` and `ProofSoundAt Z` are premises, and each is itself an assumption of
soundness: nothing here shows them (elsewhere: `keySound_at_live_holds`, `proofSoundAt_of_verify`).
Where `protocolDataWellFormed` rejects they ask nothing, and soundness holds there because the three gates reject
all. What is proved at all Z is proved here by the same theorems, at Z: the entry file's row
(`FlashProve.entrySound`, with the limits of Johnson/Goal/Conditions/EntrySits.lean), the meaning,
the extractor's equation, the error. The public files are fixed before the hash function is drawn.
No soundness is claimed here without these two premises, and none of a verifier that runs.

-/
import Johnson.Goal.TopOfTwo
import Johnson.Goal.Skeleton.ProofFile

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- Remove the default instance `Inst.Model.Scl.ref`: no statement below may pick it up silently. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Tie OnBytes.K.Arm.Pub
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open LPFD.Full (XF sBG sTG saltG KF)
open PV.EntryFive (dsF xsF)

attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF pub8 flashProveData

/-- **The body of `SoundUnderPolicyAt D eps` at one set of public files Z, read as pp.** -/
def SoundUnderPolicyAtZ (D : Description) (eps : ℕ → ℕ → ℝ≥0∞) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) :
    Prop :=
  Parser.Within (D.parse Z) honestBudget ∧ ∀ (Form : Type)
    (prove : ModelWeights (settingsOfRead pp) → D.Rand → List Token → List Token →
      RandomizedAlgorithm Form)
    (parse : Parser D Z Form) (n : ℕ), parse.Within n →
    SoundForWith (system D Z (settingsOfRead pp) Form prove parse)
      (D.extractor Z (settingsOfRead pp)) (Policy.MeetsPolicy (settingsOfRead pp) pp.pol)
      fun t => eps t n

/-- `SoundUnderPolicyAt` is that body at all Z in scope that are read. By definition. -/
theorem soundUnderPolicyAt_iff_atZ (D : Description) (eps : ℕ → ℕ → ℝ≥0∞) :
    SoundUnderPolicyAt D eps ↔ ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true →
      readFiles Z = .ok pp → SoundUnderPolicyAtZ D eps Z pp := Iff.rfl

/-- **The body of `KeySound` at Z.** -/
def KeySoundAt (Z : PublicFiles) : Prop :=
  protocolDataWellFormed (asDescriptionFiles Z) = true →
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0))

/-- **The body of `ProofSound` at Z.** -/
def ProofSoundAt (Z : PublicFiles) : Prop :=
  protocolDataWellFormed (asDescriptionFiles Z) = true →
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings theC0 theM0))

theorem keySound_iff_at : KeySound ↔ ∀ Z, InScope Z = true → KeySoundAt Z := Iff.rfl

theorem proofSound_iff_at : ProofSound ↔ ∀ Z, InScope Z = true → ProofSoundAt Z := Iff.rfl

/-- `soundUnderPolicyAt_of_toldO_or` (Johnson/Goal/SoundOr.lean) at one Z: its proof to the letter
behind "intro Z pp h₁ h₂". -/
theorem soundUnderPolicyAtZ_of_toldO_or (D : Description) (eps : ℕ → ℕ → ℝ≥0∞) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy)
    (A : ToldAtO D Z (settingsOfRead pp) (Policy.MeetsPolicy (settingsOfRead pp) pp.pol))
    (ownParser : Parser.Within (D.parse Z) honestBudget)
    (hext : D.extractor Z (settingsOfRead pp) = A.extractor)
    (bound : ∀ t n, A.err t n ≤ eps t n ∨ 1 ≤ eps t n) :
    SoundUnderPolicyAtZ D eps Z pp := by
  refine ⟨ownParser, ?_⟩
  intro Form prove parse n hn
  have key := soundForWith_system_of_toldO D Z A.c₀ A.m₀ A.T (settingsOfRead pp) A.pair A.fits
    A.claim A.Wn A.Rno A.x₀ A.εs A.core A.meaning A.noCoin A.asks A.once A.spare A.word A.code
    A.reads A.q₀ A.hq₀ A.φ A.ψ (Policy.MeetsPolicy (settingsOfRead pp) pp.pol) A.carries hext
    Form prove parse n hn
  intro cq pq St c hc p hp
  rcases bound (cq + pq) n with hb | hb
  · exact le_trans (key cq pq St c hc p hp) hb
  · exact le_trans (Prob_le_one _ _) hb

section
variable (S : (Z : PublicFiles) → DescriptionDataAtFiles (asDescriptionFiles Z)) (H : CommitterProverFormAndParser fun Z => (S Z).toDescriptionFields) (c₀ : Digest)
  (m₀ : List (Dig 256))

/-- `soundUnderPolicyAt_star` (Johnson/Goal/SoundOr.lean) at one Z. -/
theorem soundUnderPolicyAtZ_star (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (φ : (S Z).A.Mat → Option (ModelWeights (settingsOfRead pp)))
    (ψ : (S Z).A.Mat → ModelWeights (settingsOfRead pp))
    (eps : ℕ → ℕ → ℝ≥0∞)
    (hk : kThree .two (S Z).DK [] (S Z).DP ≤ KF (S Z).DK (S Z).DP)
    (bL : ∀ d ∈ dsF, (bsRound .two d.entry d.kind).b ≤ KF (S Z).DK (S Z).DP)
    (wLk : ∀ d ∈ dsF, d.entry.work ≤ 64) (own : ∀ d ∈ dsF, ∀ n ∈ d.opens, n < 2 ^ 16)
    (dL : ∀ d ∈ dsF, ∀ s ∈ d.trees, 2 ^ s.a + 2 ^ s.a ≤ 2 ^ 64)
    (wK : (S Z).DK.workFit = true) (dK : (S Z).DK.depthFit = true)
    (wP : (S Z).DP.workFit = true) (dP : (S Z).DP.depthFit = true)
    (kS : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((S Z).inputFieldsAtReadings c₀ m₀)))
    (eS : CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((S Z).inputFieldsAtReadings c₀ m₀)))
    (pS : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((S Z).inputFieldsAtReadings c₀ m₀)))
    (claim : (S Z).A.Mat → List Token → List Token → Prop)
    (meaning : ∀ i (x' : List Token × List Token) a x,
      ((S Z).inputFieldsAtReadings c₀ m₀).build x' a = some x → (∃ w, (soundnessAnalysisDataAtFullSize ((S Z).inputFieldsAtReadings c₀ m₀)).Rno i x w) →
        claim i x'.1 x'.2)
    (carries : ∀ i prompt output, claim i prompt output →
      ∃ w, φ i = some w ∧ Policy.MeetsPolicy (settingsOfRead pp) pp.pol w prompt output)
    (ownParser : Parser.Within ((descriptionOfFields (fun Z => (S Z).toDescriptionFields) H).parse Z) honestBudget)
    (hext : (S Z).ext (settingsOfRead pp) = fun commitment queryLog =>
      (((S Z).layoutsByPublicReading c₀ m₀).extractor commitment queryLog).bind φ)
    (bound : ∀ t n,
      soundnessBoundOverTypedOracles ((S Z).inputFieldsAtReadings c₀ m₀).W (soundnessAnalysisDataAtFullSize ((S Z).inputFieldsAtReadings c₀ m₀)).εs (t + (8 + n)) 0 +
        epsCode (t + (8 + n)) ≤ eps t n ∨ 1 ≤ eps t n) :
    SoundUnderPolicyAtZ (descriptionOfFields (fun Z => (S Z).toDescriptionFields) H) eps Z pp :=
  soundUnderPolicyAtZ_of_toldO_or (descriptionOfFields (fun Z => (S Z).toDescriptionFields) H) eps Z pp
    (publicReadingFitAtDescriptionOfFields S H c₀ m₀ Z (settingsOfRead pp) _ claim _ _ _ _ φ ψ
      (fun d => compilerSoundnessConditions_layoutsByPublicReading (S Z) c₀ m₀ hk bL wLk own dL wK dK wP dP kS eS pS d) meaning carries)
    ownParser hext bound

end

/-- `soundUnderPolicyAt_numbers` (Johnson/Goal/TopOfThree.lean) at one Z: the nine hypotheses on
numbers proved; the three on soundness taken where `protocolDataWellFormed` accepts. -/
theorem soundUnderPolicyAtZ_numbers (c₀ : Digest) (m₀ : List (Dig 256)) (Z : PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy)
    (φ : (dataAtFiles flashProveData Z).A.Mat → Option (ModelWeights (settingsOfRead pp)))
    (ψ : (dataAtFiles flashProveData Z).A.Mat → ModelWeights (settingsOfRead pp))
    (eps : ℕ → ℕ → ℝ≥0∞)
    (kS : protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)))
    (eS : protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)))
    (pS : protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)))
    (claim : (dataAtFiles flashProveData Z).A.Mat → List Token → List Token → Prop)
    (meaning : ∀ i (x' : List Token × List Token) a x,
      ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).build x' a = some x →
      (∃ w, (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)).Rno i x w) → claim i x'.1 x'.2)
    (carries : ∀ i prompt output, claim i prompt output →
      ∃ w, φ i = some w ∧ Policy.MeetsPolicy (settingsOfRead pp) pp.pol w prompt output)
    (hext : (dataAtFiles flashProveData Z).ext (settingsOfRead pp) = fun commitment queryLog =>
      (((dataAtFiles flashProveData Z).layoutsByPublicReading c₀ m₀).extractor commitment queryLog).bind φ)
    (bound : ∀ t n,
      soundnessBoundOverTypedOracles ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)).εs
          (t + (8 + n)) 0 + epsCode (t + (8 + n)) ≤ eps t n ∨ 1 ≤ eps t n) :
    SoundUnderPolicyAtZ (atSecondHashFunction theDescription) eps Z pp :=
  have f := frameFitFullD_parts (fit_theLay Z)
  have e := entryFit_of_test entryFitB_dsFull_140
  ofBuilt (Q := fun D => SoundUnderPolicyAtZ D eps Z pp)
    (soundUnderPolicyAtZ_star (dataAtFiles flashProveData)
      (committerAndProverWithParser (dataAtFiles flashProveData) flashProveData.honest decodeD flashProveData.f₀)
      c₀ m₀ Z pp φ ψ eps f.hk f.hE.bL e.wLk e.own e.dL f.wK f.dK f.wP f.dP
      (keySound_theLay Z c₀ m₀ kS) (entrySound_theLay Z c₀ m₀ eS) (proofSound_theLay Z c₀ m₀ pS)
      claim meaning carries (parseDec_honest (dataAtFiles flashProveData) flashProveData.honest decodeD flashProveData.f₀ Z)
      hext bound)

/-- **Soundness under the files' policy at the error `VerifierAndGoals.soundnessErrorInQueries`, at one Z, from the two
hypotheses at that Z.** The other rows are theorems at every Z and are called at Z. -/
theorem soundUnderPolicyAtZ_of_two (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (kS : KeySoundAt Z) (pS : ProofSoundAt Z) :
    SoundUnderPolicyAtZ (atSecondHashFunction theDescription) VerifierAndGoals.soundnessErrorInQueries Z pp :=
  soundUnderPolicyAtZ_numbers theC0 theM0 Z pp
    (thePhiO Z (settingsOfRead pp) (valid_of_read hr))
    (thePsi Z (settingsOfRead pp) (valid_of_read hr)) soundnessErrorInQueries kS (entrySound Z scope) pS (theClaim Z)
    (meaning Z scope) (carries Z pp scope hr) (hext Z pp scope hr)
    fun t n => (lt_or_ge (soundnessErrorInQueries t n) 1).imp (errorAtBits Z scope t n) id

/-- `soundAt_of_soundUnderPolicyAt` (Ladder/Ties.lean) at one Z: at exact match the body gives
`Sound` for every parser within n queries. General in D. -/
theorem sound_of_atZ (D : Description) (eps : ℕ → ℕ → ℝ≥0∞) (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (h : SoundUnderPolicyAtZ D eps Z pp) (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (Form : Type)
    (prove : ModelWeights (settingsOfRead pp) → D.Rand → List Token → List Token →
      RandomizedAlgorithm Form)
    (parse : Parser D Z Form) (n : ℕ) (hn : parse.Within n) :
    Sound (system D Z (settingsOfRead pp) Form prove parse) fun t => eps t n := by
  have h1 := h.2 Form prove parse n hn
  rw [exact] at h1
  have h2 := SoundForWith.mapWeights _ _ _ _ h1 (ModelWeights (settingsOfRead pp)) D.Shown
    (D.shown (settingsOfRead pp)) (modelNextToken (settingsOfRead pp))
    (D.commit Z (settingsOfRead pp)) prove id
    (system D Z (settingsOfRead pp) Form prove parse).IsModelOutput
    (fun w p o hm => ((Policy.meetsPolicy_exact_iff w p o).1 hm).2)
  have h3 : SoundForWith (system D Z (settingsOfRead pp) Form prove parse)
      (fun c q => (D.extractor Z (settingsOfRead pp) c q).map id)
      (system D Z (settingsOfRead pp) Form prove parse).IsModelOutput (fun t => eps t n) := h2
  exact (sound_iff_soundFor _ _).2 ⟨_, h3⟩

/-- **THE TOP ON SOUNDNESS AT ONE Z**: the body of `NearestSound theDescription fun t => soundnessErrorInQueries t 1`
at Z, from the two hypotheses at that Z alone. -/
theorem sound_at (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (scope : InScope Z = true)
    (hr : readFiles Z = .ok pp) (exact : pp.pol = Inst.Model.AcceptancePolicy.exact) (kS : KeySoundAt Z)
    (pS : ProofSoundAt Z) :
    Sound (systemOfRecord (atSecondHashFunction theDescription) Z (settingsOfRead pp))
      fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  sound_of_atZ _ _ Z pp (soundUnderPolicyAtZ_of_two Z pp scope hr kS pS) exact _ _ _ 1
    (theDescription_within _ Z)

/-- The form with "for all Z", back from `sound_at`: nothing is lost. -/
theorem top_sound_of_at (kS : ∀ Z, InScope Z = true → KeySoundAt Z)
    (pS : ∀ Z, InScope Z = true → ProofSoundAt Z) :
    NearestSound theDescription fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  fun Z pp scope hr exact => sound_at Z pp scope hr exact (kS Z scope) (pS Z scope)

end VerifierAndGoals.AtTheName

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
open _root_.Run
open VerifiableInference.Desc
open _root_.Run (ckP)
open TypedOracleCompiler.Joined _root_.Iop
open _root_.Compile.Joined (Chains Desc)

/-- **`ProofFileAt Z` gives `CompilerSoundnessConditionStatements.proofSound (bZ Z)` where `protocolDataWellFormed` accepts**:
`proofSound_of_proofFileAt`'s own proof (Johnson/Goal/Skeleton/ProofFile.lean) at one Z. -/
theorem proofSound_at_of_proofFileAt (Z : PublicFiles) (_hs : InScope Z = true)
    (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) (h : ProofFileAt Z) : CompilerSoundnessConditionStatements.proofSound (bZ Z) := by
  obtain ⟨XiP, FP, instP, L, hseat, R⟩ := h
  refine proofSound_record_of_rows Z _ ?_ L R
  rw [runP_the_at Z _ hseat, hl]
  rfl

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.soundUnderPolicyAt_iff_atZ
#print axioms VerifierAndGoals.AtTheName.keySound_iff_at
#print axioms VerifierAndGoals.AtTheName.proofSound_iff_at
#print axioms VerifierAndGoals.AtTheName.soundUnderPolicyAtZ_of_toldO_or
#print axioms VerifierAndGoals.AtTheName.soundUnderPolicyAtZ_star
#print axioms VerifierAndGoals.AtTheName.soundUnderPolicyAtZ_numbers
#print axioms VerifierAndGoals.AtTheName.soundUnderPolicyAtZ_of_two
#print axioms VerifierAndGoals.AtTheName.sound_of_atZ
#print axioms VerifierAndGoals.AtTheName.sound_at
#print axioms VerifierAndGoals.AtTheName.top_sound_of_at
#print axioms VerifierAndGoals.AtTheName.proofSound_at_of_proofFileAt
