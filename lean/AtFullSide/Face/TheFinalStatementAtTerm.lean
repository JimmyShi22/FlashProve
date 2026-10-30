-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Face/TheFinalStatementAtTerm.lean: the final statement at the honest part that has a value.

 1. compiledPartAtHonestProvers is what compilation adds at the protocol's honest provers; honestProversAndSettingsOf is honestProversAndSettingsAtFiles
    at it.
 2. TheFinalStatementAtTerm is the final statement of that part: of the parts of the offline prover
    and the error alone.
 3. Completeness and zero knowledge of the interactive protocol, with the error's inequality, give
    what the compiled lines ask at these provers: so FinalComplete, FinalZeroKnowledge and RepliesFit
    follow from them. It spends two of the structure's four fields. Binding and the line on the reply
    are not reached.
-/
import AtFullSide.CompletenessAndZeroKnowledge.HonestProversAndSettingsOf
import Johnson.Face.OneProtocol
import VerifiableInference.Final.ZeroKnowledgeAtTheProtocolLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Compilation
open VerifierAndGoals AtPublicFiles.AtFiles.HonestTerm
open scoped ENNReal

/-- **The final statement at the value.** -/
abbrev TheFinalStatementAtTerm (parts : (files : PublicFiles) → Parts files) (zeroKnowledgeError : ℝ≥0∞) :
    Prop :=
  TheFinalStatement parts (compiledPartAtHonestProvers parts) zeroKnowledgeError

/-- It is the final statement of honestProversAndSettingsOf. -/
theorem theFinalStatementAtTerm_eq (parts : (files : PublicFiles) → Parts files)
    (zeroKnowledgeError : ℝ≥0∞) :
    TheFinalStatementAtTerm parts zeroKnowledgeError =
      FinalStatement (honestProversAndSettingsOf parts) zeroKnowledgeError := rfl

/-- **The three statements give what the compiled lines ask.** -/
theorem termLeft_of_three (parts : (files : PublicFiles) → Parts files) (files : PublicFiles)
    (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters)
    (zeroKnowledgeError offlineStops linkStops onlineStops : ℝ≥0∞)
    (three : TheThreeIOPStatements files inUse.read (parts files) offlineStops linkStops onlineStops)
    (sum : (2⁻¹ : ℝ≥0∞) ^ 157 + (offlineStops + linkStops + (688127 : ℕ) * onlineStops) ≤
      zeroKnowledgeError) :
    TermLeft parts files parameters inUse zeroKnowledgeError :=
  ⟨offlineStops, linkStops, onlineStops,
    (completeOnServedRequests_refuse_iff files inUse.read _).1 three.complete,
    three.zeroKnowledge, sum⟩

/-- **From the three statements at every set of files in use, the compiled lines.** -/
theorem final_at_T1_of_three (parts : (files : PublicFiles) → Parts files) (zeroKnowledgeError : ℝ≥0∞)
    (three : ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters),
      ∃ offlineStops linkStops onlineStops : ℝ≥0∞,
        TheThreeIOPStatements files inUse.read (parts files) offlineStops linkStops onlineStops ∧
        (2⁻¹ : ℝ≥0∞) ^ 157 + (offlineStops + linkStops + (688127 : ℕ) * onlineStops) ≤
          zeroKnowledgeError) :
    (FinalComplete (honestProversAndSettingsOf parts) ∧
        FinalZeroKnowledge (honestProversAndSettingsOf parts) zeroKnowledgeError) ∧
      RepliesFit (honestProversAndSettingsOf parts) :=
  final_at_T1 parts zeroKnowledgeError fun files parameters inUse =>
    let ⟨offlineStops, linkStops, onlineStops, holds, sum⟩ := three files parameters inUse
    termLeft_of_three parts files parameters inUse zeroKnowledgeError offlineStops linkStops
      onlineStops holds sum

end VerifiableInference.Compilation
