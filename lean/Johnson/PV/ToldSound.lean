-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/ToldSound.lean: `innerCompiledVerifier_sound_byPublicReading` (Johnson/Top/InnerCompiledVerifierByPublicReading.lean) called at the
  value `toldOf U` (Johnson/PV/ToldMember.lean). CONDITIONAL: of its seven groups of hypotheses six
  are shown by theorems; what stays is "each": the sixteen named hypotheses at every d.

Limits: it is a call, not a result: "each" is shown at no letters. "each" is more than what is owed
  at this value: Johnson/PV/ToldLeft.lean thins it to keySound, proofSound and the meaning.

-/
import Johnson.PV.ToldMember

set_option autoImplicit false
set_option maxRecDepth 40000

noncomputable section
open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker
    OnBytes.Maker.Page _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.K.Arm OnBytes.K.Arm.Pub OnBytes.K.Arm.ProofFront OnBytes.Tie
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} {rK rP : RecFull} {depthReq : ℕ}
  {early : X → X} {salt K : ℕ} {P : (threeProtocolsWithFixedLinkAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP rK rP depthReq early
      salt).Provers}
  {T₀ : InnerCompilerInputAndAnalysisFieldsWithFixedLinkAtFullSize A E DK DP runK runP rK rP depthReq early salt K P} (U : ToldLetters T₀)

/-- **The told law at the value.** Under each (the sixteen at every d); the six added premises are
paid by theorems. Riding in U: two tests on the data, K + 2 < 2^49, the front set's three laws; in
T₀: hSeed. -/
theorem sound_toldOf (d₀ : (toldOf U).D) (Wn : Type)
    (Rno : (innerCompilerInputWithFixedLinkAtFullSize T₀).Index → (innerCompilerInputWithFixedLinkAtFullSize T₀).Instance → Wn → Prop) (x₀ : (innerCompilerInputWithFixedLinkAtFullSize T₀).Instance)
        (εs : ℝ≥0∞)
    (each : ∀ d, CompilerSoundnessConditionsWithMeaning ((toldOf U).beside Wn Rno x₀ εs d)) :
    Sound (toldOf U).system fun t => soundnessBoundOverTypedOracles (innerCompilerInputWithFixedLinkAtFullSize T₀).queryLayout εs t 0 + epsCode t :=
  innerCompiledVerifier_sound_byPublicReading (toldOf U) d₀ Wn Rno x₀ εs each (told_noCoin U) (told_asks U) (told_once U)
    (told_spare U) (told_word U) (told_code U)

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.sound_toldOf
