-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/CompletenessAndZeroKnowledge/LinesAtStoredFiles.lean: the lines of FinalStatementAtStoredFiles (Johnson/Face/AtStoredFiles.lean) that the
two statements on the interactive protocol reach, at the stored full-size public files alone.

  filesInUse_stored                    the stored files are in use, at what they read as
  lines_at_stored_files                the fields complete, zeroKnowledge and repliesFit, of honestProversAndSettingsOf parts
  finalStatementAtStoredFiles_of_ends  the structure, with the fields binding and reply as premises
  finalStatementAtStoredFiles_at_value the same at the value thePartsAt of the offline prover's arguments

Of the six fields. sound: a theorem, at every honest part (finalSound_stored). complete, zeroKnowledge: from completeness
and zero knowledge of the interactive protocol at the stored files, as their theorems end, and the inequality on the
three numbers. repliesFit: a theorem (term_repliesFit). binding, reply: premises of the theorems in this file.

Limits. Implications: completeness and zero knowledge of the interactive protocol are premises here. The error is an
argument. That the stored files pass the test on public files is the side library's (AtFullSide.Top.theLive_zFull).
That the stored files are the bytes that ship is not said. Nothing on soundness or on what is hidden.
-/
import AtFullSide.CompletenessAndZeroKnowledge.LinesAtFiles
import Johnson.Face.AtStoredFiles
import AtFullSide.Top.LiveAtFull
import E2E.KeyArgumentsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm

/-- The stored files are in use. -/
theorem filesInUse_stored : FilesInUse storedPublicFiles storedParameters :=
  ⟨filesTaken_stored, AtFullSide.Top.theLive_zFull⟩

variable (parts : (files : PublicFiles) → Parts files)

/-- **Three lines at the stored files**, from the two statements there as their theorems end. -/
theorem lines_at_stored_files {zeroKnowledgeError offlineStops linkStops onlineStops : ℝ≥0∞}
    (complete : AtPublicFiles.AtFiles.HonestTerm.CompleteAtFiles storedPublicFiles (parts storedPublicFiles) filesTaken_stored.read)
    (zeroKnowledge : ZeroKnowledgeOnServedRequests storedPublicFiles filesTaken_stored.read
      (HonestProvers.ofThreeProvers (honestProvers storedPublicFiles (parts storedPublicFiles))) offlineStops linkStops onlineStops)
    (sum : (2⁻¹ : ℝ≥0∞) ^ 157 + (offlineStops + linkStops + (688127 : ℕ) * onlineStops) ≤
      zeroKnowledgeError) :
    VerifiableInference.Compilation.CompleteAtFiles (honestProversAndSettingsOf parts) storedPublicFiles storedParameters ∧
      ZeroKnowledgeAtFiles (honestProversAndSettingsOf parts) zeroKnowledgeError storedPublicFiles storedParameters ∧
      RepliesFitAtFiles (honestProversAndSettingsOf parts) storedPublicFiles storedParameters :=
  lines_at_files_of_ends parts storedPublicFiles storedParameters filesInUse_stored complete zeroKnowledge sum

/-- **The six lines at the stored files**: four reached, two asked. -/
theorem finalStatementAtStoredFiles_of_ends
    {zeroKnowledgeError offlineStops linkStops onlineStops : ℝ≥0∞}
    (complete : AtPublicFiles.AtFiles.HonestTerm.CompleteAtFiles storedPublicFiles (parts storedPublicFiles) filesTaken_stored.read)
    (zeroKnowledge : ZeroKnowledgeOnServedRequests storedPublicFiles filesTaken_stored.read
      (HonestProvers.ofThreeProvers (honestProvers storedPublicFiles (parts storedPublicFiles))) offlineStops linkStops onlineStops)
    (sum : (2⁻¹ : ℝ≥0∞) ^ 157 + (offlineStops + linkStops + (688127 : ℕ) * onlineStops) ≤
      zeroKnowledgeError)
    (notReachedBinding : BindingAtFiles (honestProversAndSettingsOf parts) storedPublicFiles storedParameters)
    (notReachedReply : ReplyAtFiles (honestProversAndSettingsOf parts) storedPublicFiles storedParameters) :
    FinalStatementAtStoredFiles (honestProversAndSettingsOf parts) zeroKnowledgeError where
  sound := finalSound_stored (honestProversAndSettingsOf parts)
  binding := notReachedBinding
  complete := (lines_at_stored_files parts complete zeroKnowledge sum).1
  zeroKnowledge := (lines_at_stored_files parts complete zeroKnowledge sum).2.1
  reply := notReachedReply
  repliesFit := (lines_at_stored_files parts complete zeroKnowledge sum).2.2

/-- **The same at the value of the offline prover's arguments.** -/
theorem finalStatementAtStoredFiles_at_value
    {zeroKnowledgeError offlineStops linkStops onlineStops : ℝ≥0∞}
    (complete : AtPublicFiles.AtFiles.HonestTerm.CompleteAtFiles storedPublicFiles (thePartsAt storedPublicFiles) filesTaken_stored.read)
    (zeroKnowledge : ZeroKnowledgeOnServedRequests storedPublicFiles filesTaken_stored.read
      (HonestProvers.ofThreeProvers (honestProvers storedPublicFiles (thePartsAt storedPublicFiles))) offlineStops linkStops onlineStops)
    (sum : (2⁻¹ : ℝ≥0∞) ^ 157 + (offlineStops + linkStops + (688127 : ℕ) * onlineStops) ≤
      zeroKnowledgeError)
    (notReachedBinding : BindingAtFiles (honestProversAndSettingsOf thePartsAt) storedPublicFiles storedParameters)
    (notReachedReply : ReplyAtFiles (honestProversAndSettingsOf thePartsAt) storedPublicFiles storedParameters) :
    FinalStatementAtStoredFiles (honestProversAndSettingsOf thePartsAt) zeroKnowledgeError :=
  finalStatementAtStoredFiles_of_ends thePartsAt complete zeroKnowledge sum notReachedBinding
    notReachedReply

/-- Each reached line, laid into the structure's own field type. -/
example {zeroKnowledgeError offlineStops linkStops onlineStops : ℝ≥0∞}
    (F : FinalStatementAtStoredFiles (honestProversAndSettingsOf parts) zeroKnowledgeError)
    (complete : AtPublicFiles.AtFiles.HonestTerm.CompleteAtFiles storedPublicFiles (parts storedPublicFiles) filesTaken_stored.read)
    (zeroKnowledge : ZeroKnowledgeOnServedRequests storedPublicFiles filesTaken_stored.read
      (HonestProvers.ofThreeProvers (honestProvers storedPublicFiles (parts storedPublicFiles))) offlineStops linkStops onlineStops)
    (sum : (2⁻¹ : ℝ≥0∞) ^ 157 + (offlineStops + linkStops + (688127 : ℕ) * onlineStops) ≤
      zeroKnowledgeError) :
    FinalStatementAtStoredFiles (honestProversAndSettingsOf parts) zeroKnowledgeError :=
  { F with
    sound := finalSound_stored (honestProversAndSettingsOf parts)
    complete := (lines_at_stored_files parts complete zeroKnowledge sum).1
    zeroKnowledge := (lines_at_stored_files parts complete zeroKnowledge sum).2.1
    repliesFit := (lines_at_stored_files parts complete zeroKnowledge sum).2.2 }

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.filesInUse_stored
#print axioms VerifiableInference.Compilation.lines_at_stored_files
#print axioms VerifiableInference.Compilation.finalStatementAtStoredFiles_of_ends
#print axioms VerifiableInference.Compilation.finalStatementAtStoredFiles_at_value
