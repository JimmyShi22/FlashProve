-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/EntryAtWritten.lean: THE PREMISE ON THE ENTRY FILE OF THE REDUCTION (CompilerSoundnessConditionStatements.entrySound), AT THE WRITTEN VALUE FOR THE SLOT: the like of entrySoundOfFullD_rootV_all (EntryAtSlotV.lean, which is not in this library), WITHOUT InScope, WITHOUT THE ELDER ROOT,
UNDER hSP ALONE (K1's sending's law at the link: PAID in EntryWrittenPaid.lean):
  entrySoundOfFullD_written   AT EVERY PARAMETER FILE pol (linkDecisionAtParameterFile TAKES TWO VALUES IN ALL: «no to all» · one closed run: the ∀ is over these two) AND EVERY GATE b: dec = gatedLinkDecision b (Desc.K15.linkDecisionAtParameterFile pol) → CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T), at the frame's own letters dsFull · frD.xs
BY: decWritten_is (no to all, or decDescFullV frP ‹plan› ‹Bool› ∘ recX) · entrySoundOfFullD_typedV (any plan, any Bool) · entrySoundOfFullD_of_never.
LIMITS THAT TRAVEL: the statement on codes is filled by Cb.Gl.bchks46At (lean/LIMITS.md, L15) · the bound counts work · an interactive protocol's round-by-round soundness, at the full size · it says no goal of any
verifier that runs. OBJECT: Desc.K15.linkDecisionAtParameterFile · USER: entrySoundOfFullD_written_paid (EntryWrittenPaid.lean) · LETTERS: the reduction's own.
-/
import Johnson.Goal.Conditions.EntryWrittenLaw
import Johnson.Goal.Conditions.EntryAtTypedV
import Johnson.Flat.Dec.FailsClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open TypedOracleCompiler.Slice
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Desc.K15 (SendPOfDecide frP decDescFullV linkDeclaredRounds linkRoundsMatchPlan linkDecisionAtParameterFile)

section Full
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} {rK rP : RecFull}
  {depthReq : ℕ} {early : X → X} {salt K : ℕ}

/-- **At the written value, at every parameter file.** -/
theorem entrySoundOfFullD_written (hSP : SendPOfDecide) (pol : ByteArray) {b : Bool} {dec : RecFull × RecFull → PQ.View → Bool}
    (er : dec = gatedLinkDecision b (linkDecisionAtParameterFile pol))
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP dsFull frD.xs dec rK rP depthReq early
      salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP dsFull frD.xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T) := by
  cases hb : b with
  | false =>
    refine entrySoundOfFullD_of_never (fun rr v => ?_) T
    rw [er, hb]
    rfl
  | true =>
    rcases _root_.Desc.K15.decWritten_is pol with h | h
    · refine entrySoundOfFullD_of_never (fun rr v => ?_) T
      rw [er, h]
      simp [gatedLinkDecision]
    · exact entrySoundOfFullD_typedV hSP (linkDeclaredRounds frP)
        (linkRoundsMatchPlan frP OnBytes.Params.recordPlan) hb (er.trans (by rw [h]; rfl)) T

end Full

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.entrySoundOfFullD_written
