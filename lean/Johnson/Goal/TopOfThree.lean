-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/TopOfThree.lean: the top row on soundness, with the level, at the name
`VerifierAndGoals.theDescription`, from three hypotheses.

The rows are those of Johnson/Goal/Conditions/RowsAtTheRecord.lean. Of its nine, `Carries`,
`ErrorAtBits`, `RoundErrorSmall` and `CountSmall` are theorems there. Here two more are:
  `meaning`: by `meaning_the` (Johnson/Goal/Conditions/SoundAtThe.lean).
  `hext`: by `hext_the` (Johnson/Goal/Description/Hext.lean).
  `verifierIsWithin`: the verifier's own queries stay within the allowance of the goals with a
    level.
So three are left here (Limits, 1): `KeySound`, `EntrySound`, `ProofSound`.
  `soundUnderPolicyAt_of_three`: soundness under the files' policy at the error `VerifierAndGoals.soundnessErrorInQueries`.
  `g8bits_of_three`: `G8bits`, the goal with the level.
  `top_sound_of_three`: `Sound` in its nearest form at fun t => `VerifierAndGoals.soundnessErrorInQueries` t 1.

Limits. (1) The three are hypotheses here. Elsewhere in this tree: `KeySound` is a theorem
(`keySound_holds`, Johnson/Goal/Conditions/KeyOpenHolds.lean); so is `EntrySound`
(`FlashProve.entrySound`, Johnson/Goal/Conditions/EntrySits.lean); the body of `ProofSound` is one
at each Z in scope whose files are read (`proofSoundAt_of_verify`,
Johnson/Goal/Skeleton/SoundOfVerifyMore.lean), and these are all: `ProofSound` itself is
`proofSound_of_verify` (SoundOfVerifyGoals.lean, in that folder). Each of the three speaks only
where `protocolDataWellFormed` says yes, see (4). The limits in these four files' heads travel. (2) What stands in
the description's three slots is told in Johnson/Goal/Description/KeyFold.lean, ProofFold.lean and
LinkDec.lean. Of no verifier that runs is it shown here that it is sound. (3) The named side's bound
on a round's error, 1 / 2^128, is a letter, no price; its own extractor, that extractor's error 0
and its next token are place-holders: a walk by program over these statements' terms finds no reader
of the first two, and the verifier is the same at every value of the third. (4) Where `protocolDataWellFormed` says
no the three ask nothing, and soundness holds there because the three gates refuse all. That
`protocolDataWellFormed` says yes at the release's two stored sets of public files has been evaluated, by a run at
the place-holder data of another text, not proved. Proved of the library's written copies alone:
at `VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap` (`theLive_zFull`, `theLive_zGap`) and, within four bounds on the
policy, at `VerifierAndGoals.zAt` (`theLive_zAt`): AtFullSide/Top/, a side library. (5) How far they are met:
see (1).
-/
import Johnson.Goal.Conditions.RowsAtTheRecord
import Johnson.Goal.Conditions.SoundAtThe
import Johnson.Goal.Description.Hext
import Johnson.Goal.SoundOr
import Ladder.BitsTies
import Ladder.PackageTies

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

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

/-- G8_theDescription_numbers (Johnson/Goal/Conditions/NumbersAtThe.lean), with
`SoundUnderPolicyAt … eps` for `G8`: the nine debts on numbers paid; the three on soundness asked
where the test says yes. -/
theorem soundUnderPolicyAt_numbers (c₀ : Digest) (m₀ : List (Dig 256))
    (φO : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → settingsAreValid s = true →
      (dataAtFiles flashProveData Z).A.Mat → Option (ModelWeights s))
    (ψ : (Z : PublicFiles) → (s : IntegerTransformer.Settings) → settingsAreValid s = true →
      (dataAtFiles flashProveData Z).A.Mat → ModelWeights s)
    (eps : ℕ → ℕ → ℝ≥0∞)
    (kS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)))
    (eS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)))
    (pS : ∀ Z, InScope Z = true → protocolDataWellFormed (asDescriptionFiles Z) = true →
      CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)))
    (claim : (Z : PublicFiles) → (dataAtFiles flashProveData Z).A.Mat → List Token → List Token → Prop)
    (meaning : ∀ Z, InScope Z = true → ∀ i (x' : List Token × List Token) a x,
      ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).build x' a = some x →
      (∃ w, (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)).Rno i x w) → claim Z i x'.1 x'.2)
    (carries : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → ∀ hr : readFiles Z = .ok pp,
      ∀ i prompt output, claim Z i prompt output →
        ∃ w, φO Z (settingsOfRead pp) (valid_of_read hr) i = some w ∧
          Policy.MeetsPolicy (settingsOfRead pp) pp.pol w prompt output)
    (hext : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → ∀ hr : readFiles Z = .ok pp,
      (dataAtFiles flashProveData Z).ext (settingsOfRead pp) = fun commitment queryLog =>
        (((dataAtFiles flashProveData Z).layoutsByPublicReading c₀ m₀).extractor commitment queryLog).bind
          (φO Z (settingsOfRead pp) (valid_of_read hr)))
    (bound : ∀ Z, InScope Z = true → ∀ t n,
      soundnessBoundOverTypedOracles ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀).W (soundnessAnalysisDataAtFullSize ((dataAtFiles flashProveData Z).inputFieldsAtReadings c₀ m₀)).εs
          (t + (8 + n)) 0 + epsCode (t + (8 + n)) ≤ eps t n ∨ 1 ≤ eps t n) :
    SoundUnderPolicyAt (atSecondHashFunction theDescription) eps :=
  have f := fun Z => frameFitFullD_parts (fit_theLay Z)
  have e := entryFit_of_test entryFitB_dsFull_140
  ofBuilt (Q := fun D => SoundUnderPolicyAt D eps)
    (soundUnderPolicyAt_star (dataAtFiles flashProveData)
      (committerAndProverWithParser (dataAtFiles flashProveData) flashProveData.honest decodeD flashProveData.f₀)
      c₀ m₀ φO ψ eps (fun Z _ => (f Z).hk) (fun Z _ => (f Z).hE.bL) e.wLk e.own e.dL
      (fun Z _ => (f Z).wK) (fun Z _ => (f Z).dK) (fun Z _ => (f Z).wP) (fun Z _ => (f Z).dP)
      (fun Z s => keySound_theLay Z c₀ m₀ (kS Z s)) (fun Z s => entrySound_theLay Z c₀ m₀ (eS Z s))
      (fun Z s => proofSound_theLay Z c₀ m₀ (pS Z s)) claim meaning carries
      (fun Z _ _ _ => parseDec_honest (dataAtFiles flashProveData) flashProveData.honest decodeD flashProveData.f₀ Z) hext bound)

/-- The list's row verifier_within, at the name. -/
def VerifierIsWithin : Prop := VerifierWithin (atSecondHashFunction theDescription)

/-- The seven rows give soundness under the files' policy AT THE ERROR `soundnessErrorInQueries`, at the name. -/
theorem soundUnderPolicyAt_bits (kS : KeySound) (eS : EntrySound) (pS : ProofSound) (hM : Meaning)
    (hC : Carries) (hX : Hext) (hE : ErrorAtBits) :
    SoundUnderPolicyAt (atSecondHashFunction theDescription) soundnessErrorInQueries :=
  soundUnderPolicyAt_numbers theC0 theM0 thePhiO thePsi soundnessErrorInQueries kS eS pS theClaim hM hC hX
    fun Z hZ t n => (lt_or_ge (soundnessErrorInQueries t n) 1).imp (hE Z hZ t n) id

/-- **VerifierIsWithin is a theorem at the name**: the further public reading asks at most seven
times; the description's own parser once; the compiled verifier's own count is at most 2^20. -/
theorem verifierIsWithin : VerifierIsWithin := by
  refine ofBuilt (Q := VerifierWithin) ?_
  intro Z _
  refine ⟨7, 1, fun c => ?_, descriptionOfDataOnBytes_within flashProveData Z, fun c m => ?_⟩
  · have hl : (ssOf (par7 recordGround Z.pol Z.KL Z.lay) c).length ≤ 7 := by
      unfold ssOf par7
      rw [List.length_map]
      split <;> simp
    have g : ((descriptionOfDataOnBytes flashProveData).readMore Z c).toRandomized.QueryBound 7 := by
      rw [readMore_built]
      exact queryBound_mono_det _ _ _ hl (queryBound_asks _)
    exact g
  · have h := count_the Z c m
    have e := input_W flashProveData Z c m
    have g : 2 + 7 + 1 + tVC ((descriptionOfDataOnBytes flashProveData).input Z c m).queryLayout ≤ verifierQueryAllowance := by
      rw [e]
      unfold verifierQueryAllowance
      omega
    exact g

end VerifierAndGoals.AtTheName

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD

/-- **The row on the meaning is a theorem at the name**: by `meaning_the`. It holds whatever the
three decisions are. -/
theorem meaning : Meaning :=
  fun Z _ i x' a x hb hw => ⟨lawful_ppAtFiles _ _, meaning_the Z i x' a x hb hw⟩

/-- **The row on the extractor is a theorem at the name**: `hext_the`. -/
theorem hext : Hext := hext_the

/-- **Three rows give soundness under the files' policy at the error `VerifierAndGoals.soundnessErrorInQueries`.** -/
theorem soundUnderPolicyAt_of_three (kS : KeySound) (eS : EntrySound) (pS : ProofSound) :
    SoundUnderPolicyAt (atSecondHashFunction theDescription) VerifierAndGoals.soundnessErrorInQueries :=
  soundUnderPolicyAt_bits kS eS pS meaning carries hext errorAtBits

/-- **Three rows give G8bits, the goal with the level, at the name.** -/
theorem g8bits_of_three (kS : KeySound) (eS : EntrySound) (pS : ProofSound) :
    G8bits theDescription :=
  ⟨verifierIsWithin, soundUnderPolicyAt_of_three kS eS pS⟩

/-- **Three rows give the top row on soundness at the error fun t => `VerifierAndGoals.soundnessErrorInQueries` t 1**: the
description's own parser asks once (`theDescription_within`). -/
theorem top_sound_of_three (kS : KeySound) (eS : EntrySound) (pS : ProofSound) :
    NearestSound theDescription fun t => VerifierAndGoals.soundnessErrorInQueries t 1 :=
  fun Z pp scope read exact =>
    ((soundAt_of_soundUnderPolicyAt _ _ (soundUnderPolicyAt_of_three kS eS pS)) Z pp scope
      read exact).2 _ _ _ 1 (theDescription_within _ Z)

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.meaning
#print axioms VerifierAndGoals.AtTheName.hext
#print axioms VerifierAndGoals.AtTheName.verifierIsWithin
#print axioms VerifierAndGoals.AtTheName.soundUnderPolicyAt_of_three
#print axioms VerifierAndGoals.AtTheName.g8bits_of_three
#print axioms VerifierAndGoals.AtTheName.top_sound_of_three
