-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/EntryWrittenPaid.lean: THE PAYER AT THE WRITTEN VALUE WITH ITS PREMISE ON K1's SENDING PAID (Desc.K15.sendPOfDecide: Johnson/Desc/K15/SendOwnPaid.lean, over Johnson/Desc/K1/Law/SendP3.lean): the like of EntryAtRootPaid.lean, which is not in this library.
  entrySoundOfFullD_written_paid    AT EVERY PARAMETER FILE AND EVERY GATE: dec = gatedLinkDecision b (Desc.K15.linkDecisionAtParameterFile pol) → CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T): no premise in the binders but the equation (THE STATEMENT ON CODES IS FILLED INSIDE by Cb.Gl.bchks46At: a limit that travels)
OBJECT: Desc.K15.linkDecisionAtParameterFile · USER: hole_entrySound (EntrySits.lean) · LETTERS: the reduction's own. The limits that travel: EntryAtWritten.lean's.
-/
import Johnson.Goal.Conditions.EntryAtWritten
import Johnson.Desc.K15.SendOwnPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open TypedOracleCompiler.Slice
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Desc.K15 (linkDecisionAtParameterFile)

section Full
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
  {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
  {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} {rK rP : RecFull}
  {depthReq : ℕ} {early : X → X} {salt K : ℕ}

theorem entrySoundOfFullD_written_paid (pol : ByteArray) {b : Bool} {dec : RecFull × RecFull → PQ.View → Bool}
    (er : dec = gatedLinkDecision b (linkDecisionAtParameterFile pol))
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP dsFull frD.xs dec rK rP depthReq early
      salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP dsFull frD.xs dec rK rP depthReq early salt K P) :
    CompilerSoundnessConditionStatements.entrySound (soundnessAnalysisDataAtFullSize T) :=
  entrySoundOfFullD_written _root_.Desc.K15.sendPOfDecide pol er T

end Full

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.entrySoundOfFullD_written_paid
