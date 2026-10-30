-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/NumbersAtThe.lean: at the one closed term `VerifierAndGoals.theDescription`
(Johnson/Goal/Description/Description.lean): of the premises of `G8_theDescription`
(Johnson/Goal/Description/JointD.lean)
the nine on numbers are proved, at every set of public files, and the three hypotheses on soundness
are asked only where the test `protocolDataWellFormed` says yes. Theorems; no definition.

Main names.
  `fit_built`, `fit_theLay`: the one test on numbers (`sizeNumbersFitAtFullSize`,
    Johnson/Flat/Dec/FailsClosed.lean) says yes at the letters of `dataAtFiles flashProveData Z`, at every Z.
    Where `protocolDataWellFormed` says yes, that is its own yes. Where it says no, the record stands at the plan
    without depth, two whole files without a round, the entry file's written rounds and K = 140
    (`frameFitFullD_dead`, `kf_dead`).
  `runK_built`, `runP_built`, `dec_built`: in both branches the three decisions are the record's
    own gates. General in the record.
  `keySound_theLay`, `entrySound_theLay`, `proofSound_theLay`: each of the three hypotheses on
    soundness follows from itself where `protocolDataWellFormed` says yes. Where it says no the gate is shut, the
    decision never says yes, and the hypothesis holds for nothing.
  `G8_theDescription_numbers`: `G8 theDescription` from: eps, ceil, bound; the three hypotheses on
    soundness where `protocolDataWellFormed` says yes; claim, meaning, carries, hext.

Limits. A conditional statement. Where `protocolDataWellFormed` says no the verifier refuses everything: the
statement is true and empty there, and it counts only beside "`protocolDataWellFormed` says yes at the release's
files", which is an evaluation and no theorem of this file. All limits of
Johnson/Goal/Description/JointD.lean
hold here. On the three premises on soundness see limit (1) in the head of
Johnson/Goal/TopOfThree.lean.
No soundness of a verifier is claimed. Nothing on hiding.
`theLay_hl` reads the frame's test out of `protocolDataWellFormed` by `theLive_frame`, which stands beside
`protocolDataWellFormed`. The plan of which the depths are read is the record's own field `DescriptionData.G` (at `flashProveData`:
`thePlan`).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Description.JointD
import Johnson.Goal.Tie.TieSmallFacts
import Johnson.Flat.Dec.ClosedAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

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

/- From here to `dec_built`: `dataAtFiles` lays its branch in the data, so `builtS_dead` goes by
`dataAtFilesFromRounds_congr` and the three lemmas `…_built` are `rfl`. `fit_theLay` is stated at a letter L first
(`fit_built`) and then called, so that Lean does not unfold `protocolDataWellFormed`. -/
theorem builtS_dead (L : DescriptionData) (Z : PublicFiles) (h : ¬ L.live (asDescriptionFiles Z) = true) :
    dataAtFiles L Z = dataAtFilesFromRounds L (asDescriptionFiles Z) (L.Gd (asDescriptionFiles Z)) emptyRoundsData emptyRoundsData fit3_empty := by
  have h' : L.live (asDescriptionFiles Z) = false := by simpa using h
  exact dataAtFilesFromRounds_congr L _ (by unfold DescriptionData.filesParametersOrDefault; rw [h']; rfl) (by unfold DescriptionData.keyRoundsOrEmpty; rw [h']; rfl)
    (by unfold DescriptionData.proofRoundsOrEmpty; rw [h']; rfl) _ _

/-- The test at the family's letters, at a letter L. -/
theorem fit_built (L : DescriptionData) (v : ℕ) (hv : 13555 ≤ v)
    (hl : ∀ Zk, L.live Zk = true → sizeNumbersFitAtFullSize (KF (L.DK Zk) (L.DP Zk)) v (L.G
                   Zk).c.first.binding.logLeaves
      (L.G Zk).k.oneTime.binding.logLeaves (L.DK Zk) (L.DP Zk) dsFull frD.xs = true)
    (hd₁ : ∀ Zk, (L.Gd Zk).c.first.binding.logLeaves = 0) (hd₂ : ∀ Zk, (L.Gd
        Zk).k.oneTime.binding.logLeaves = 0)
    (Z : PublicFiles) :
    sizeNumbersFitAtFullSize (KF (dataAtFiles L Z).DK (dataAtFiles L Z).DP) v
      (dataAtFiles L Z).G.c.first.binding.logLeaves (dataAtFiles L Z).G.k.oneTime.binding.logLeaves
      (dataAtFiles L Z).DK (dataAtFiles L Z).DP dsFull frD.xs = true := by
  by_cases h : L.live (asDescriptionFiles Z) = true
  · rw [builtS_live L Z h]
    exact hl _ h
  · rw [builtS_dead L Z h]
    show sizeNumbersFitAtFullSize (KF emptyRoundsData emptyRoundsData) v (L.Gd (asDescriptionFiles Z)).c.first.binding.logLeaves
      (L.Gd (asDescriptionFiles Z)).k.oneTime.binding.logLeaves deadW deadW dsFull frD.xs = true
    rw [kf_dead, hd₁, hd₂]
    exact frameFitFullD_dead (le_refl _) (by norm_num) hv

/-- flashProveData's test gives the frame's test at flashProveData's data. -/
theorem theLay_hl (Zk : OnBytes.K.Pub) (h : flashProveData.live Zk = true) :
    sizeNumbersFitAtFullSize (KF (flashProveData.DK Zk) (flashProveData.DP Zk)) theQueries (flashProveData.G
                                   Zk).c.first.binding.logLeaves
      (flashProveData.G Zk).k.oneTime.binding.logLeaves (flashProveData.DK Zk) (flashProveData.DP Zk) dsFull frD.xs = true
          := by
  have h1 := theLive_frame Zk h
  unfold VerifiableInference.OnPublicFiles.sizeNumbersFitAtPlan at h1
  exact h1

theorem theLay_hd₁ (Zk : OnBytes.K.Pub) : (flashProveData.Gd Zk).c.first.binding.logLeaves = 0 :=
    FilesParameters.noDepth_first (thePlan Zk)

theorem theLay_hd₂ (Zk : OnBytes.K.Pub) : (flashProveData.Gd Zk).k.oneTime.binding.logLeaves = 0 :=
    FilesParameters.noDepth_oneTime (thePlan Zk)

attribute [local irreducible] flashProveData in
/-- **The one test on numbers says yes at the family's letters, at every Z.** -/
theorem fit_theLay (Z : PublicFiles) :
    sizeNumbersFitAtFullSize (KF (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP) theQueries
      (dataAtFiles flashProveData Z).G.c.first.binding.logLeaves (dataAtFiles flashProveData Z).G.k.oneTime.binding.logLeaves
      (dataAtFiles flashProveData Z).DK (dataAtFiles flashProveData Z).DP dsFull frD.xs = true :=
  fit_built flashProveData theQueries (by unfold theQueries; norm_num) theLay_hl theLay_hd₁ theLay_hd₂ Z

theorem runK_built (L : DescriptionData) (Z : PublicFiles) : (dataAtFiles L Z).runK = L.runK (asDescriptionFiles Z) := rfl

theorem runP_built (L : DescriptionData) (Z : PublicFiles) : (dataAtFiles L Z).runP = L.runP (asDescriptionFiles Z) := rfl

theorem dec_built (L : DescriptionData) (Z : PublicFiles) : (dataAtFiles L Z).dec = L.dec (asDescriptionFiles Z) := rfl

theorem keySound_theLay (Z : PublicFiles) (c₀ : Digest) (m₀ : List (Dig 256))
    (k : protocolDataWellFormed (asDescriptionFiles Z) = true → CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀
                                                                               m₀))) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)) := by
  cases h : protocolDataWellFormed (asDescriptionFiles Z) with
  | true => exact k h
  | false =>
    refine keySoundOfFullD_of_never (fun r v₁ v₂ v₃ => ?_) _
    rw [runK_built]
    exact gate3_dead h (theKeyRun (asDescriptionFiles Z)) r v₁ v₂ v₃

theorem entrySound_theLay (Z : PublicFiles) (c₀ : Digest) (m₀ : List (Dig 256))
    (k : protocolDataWellFormed (asDescriptionFiles Z) = true → CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀
                                                                               m₀))) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)) := by
  cases h : protocolDataWellFormed (asDescriptionFiles Z) with
  | true => exact k h
  | false =>
    refine entrySoundOfFullD_of_never (fun rr v => ?_) _
    rw [dec_built]
    exact gate1_dead h (linkDecisionAtFiles (asDescriptionFiles Z)) rr v

theorem proofSound_theLay (Z : PublicFiles) (c₀ : Digest) (m₀ : List (Dig 256))
    (k : protocolDataWellFormed (asDescriptionFiles Z) = true → CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀
                                                                               m₀))) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)) := by
  cases h : protocolDataWellFormed (asDescriptionFiles Z) with
  | true => exact k h
  | false =>
    refine proofSoundOfFullD_of_never (fun x v₁ v₂ v₃ => ?_) _
    rw [runP_built]
    exact gate3_dead h (theProofRun (asDescriptionFiles Z)) x v₁ v₂ v₃

/-- **G8 at the description: the nine hypotheses on numbers proved; the three on soundness taken
where the test says yes.** -/
theorem G8_theDescription_numbers (c₀ : Digest) (m₀ : List (Dig 256))
    (φO : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → settingsAreValid s = true →
      (dataAtFiles flashProveData Z).A.Mat → Option (ModelWeights s))
    (ψ : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → settingsAreValid s = true →
      (dataAtFiles flashProveData Z).A.Mat → ModelWeights s)
    (eps : ℕ → ℕ → ℝ≥0∞)
    (ceil : ∀ t n, t ≤ queryBudget → n ≤ parserBudget → eps t n ≤ ceiling)
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)))
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
    G8 theDescription :=
  have f := fun Z => frameFitFullD_parts (fit_theLay Z)
  have e := entryFit_of_test entryFitB_dsFull_140
  G8_theDescription c₀ m₀ φO ψ eps ceil (fun Z _ => (f Z).hk) (fun Z _ => (f Z).hE.bL) e.wLk e.own
      e.dL
    (fun Z _ => (f Z).wK) (fun Z _ => (f Z).dK) (fun Z _ => (f Z).wP) (fun Z _ => (f Z).dP)
    (fun Z s => keySound_theLay Z c₀ m₀ (kS Z s)) (fun Z s => entrySound_theLay Z c₀ m₀ (eS Z s))
    (fun Z s => proofSound_theLay Z c₀ m₀ (pS Z s)) claim meaning carries hext bound

end FlashProve

#print axioms FlashProve.fit_theLay
#print axioms FlashProve.keySound_theLay
#print axioms FlashProve.entrySound_theLay
#print axioms FlashProve.proofSound_theLay
#print axioms FlashProve.G8_theDescription_numbers
