-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Face/TheStoredLines.lean: the six lines at the stored files, at the honest part.

 1. Soundness, binding, the reply and the replies' numbers are theorems there.
 2. Completeness and zero knowledge follow from the two statements at the interactive level, at the
    stored files alone, with the error's inequality.
 3. Nothing here proves either statement: they and the inequality are the premises that are left.
-/
import AtFullSide.Face.HonestProversAndSettingsValue
import AtFullSide.CompletenessAndZeroKnowledge.LinesAtStoredFiles
import AtFullSide.Face.FinalBindingAtTheValue

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Compilation
open VerifierAndGoals FlashProve AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open scoped ENNReal

/-- **The six lines at the stored files, at every offline part**: the premises left are the two statements
and the inequality. -/
theorem statementAtStoredFiles_of_parts (parts : (files : PublicFiles) → Parts files)
    {zeroKnowledgeError offlineStops linkStops onlineStops : ℝ≥0∞}
    (complete : AtPublicFiles.AtFiles.HonestTerm.CompleteAtFiles storedPublicFiles (parts storedPublicFiles) filesTaken_stored.read)
    (zeroKnowledge : ZeroKnowledgeOnServedRequests storedPublicFiles filesTaken_stored.read
      (HonestProvers.ofThreeProvers (honestProvers storedPublicFiles (parts storedPublicFiles))) offlineStops linkStops onlineStops)
    (sum : (2⁻¹ : ℝ≥0∞) ^ 157 + (offlineStops + linkStops + (688127 : ℕ) * onlineStops) ≤
      zeroKnowledgeError) :
    FinalStatementAtStoredFiles (honestProversAndSettingsOf parts) zeroKnowledgeError :=
  have lines := lines_at_stored_files parts complete zeroKnowledge sum
  ⟨finalSound_stored (honestProversAndSettingsOf parts),
    finalSoundAndBinding_termHonest parts storedPublicFiles storedParameters filesInUse_stored, lines.1, lines.2.1,
    finalHandsOutNoProof_term parts storedPublicFiles storedParameters filesTaken_stored, lines.2.2⟩

/-- **The same at the honest part.** -/
theorem statementAtStoredFiles
    {zeroKnowledgeError offlineStops linkStops onlineStops : ℝ≥0∞}
    (complete : AtPublicFiles.AtFiles.HonestTerm.CompleteAtFiles storedPublicFiles (thePartsAt storedPublicFiles)
      filesTaken_stored.read)
    (zeroKnowledge : ZeroKnowledgeOnServedRequests storedPublicFiles filesTaken_stored.read
      (HonestProvers.ofThreeProvers (honestProvers storedPublicFiles (thePartsAt storedPublicFiles))) offlineStops linkStops onlineStops)
    (sum : (2⁻¹ : ℝ≥0∞) ^ 157 + (offlineStops + linkStops + (688127 : ℕ) * onlineStops) ≤
      zeroKnowledgeError) :
    FinalStatementAtStoredFiles honestProversAndSettings zeroKnowledgeError :=
  statementAtStoredFiles_of_parts thePartsAt complete zeroKnowledge sum

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.statementAtStoredFiles_of_parts
#print axioms VerifiableInference.Compilation.statementAtStoredFiles
