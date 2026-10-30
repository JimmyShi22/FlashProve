-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/TheWorstCaseCheckCanBeMet.lean

The premise of the statement in AtFullSide/E2E/CompleteWhereTheWorstCaseCheckPasses.lean can be met
at all public files in use. It states no goal.

* `SomeWeightsPassAtAllValidSettings`: at all valid settings there are weights that pass the check
  (`PassesWorstCaseCheck`, VerifiableInference/Bounds/NeverFails.lean).
  `someWeightsPassAtAllValidSettings`: it holds, by `exists_passesWorstCaseCheck`
  (VerifiableInference/Bounds/SomeWeightsPassAtValidSettings.lean).
* `some_weights_pass_at_all_files_in_use`: under it, at all public files in use there are weights
  that pass the check, and of these weights the conclusion of
  `theHonestPart_complete_where_the_worst_case_check_passes` holds. The settings that public files
  read as are valid (`valid_of_read`, Ladder/Ties.lean).
* `at_all_files_in_use_some_weights_pass`: the same with no hypothesis but that the files are in
use.

Limits. It shows that the premise can be met, and no more. The weights that the proof gives have 0
at every place: their layers compute nothing. Nothing is said of the converted weights of a real
model.
-/
import AtFullSide.E2E.CompleteWhereTheWorstCaseCheckPasses
import VerifiableInference.Bounds.SomeWeightsPassAtValidSettings

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open VerifiableInference.AtEveryRequest (HonestProofRejectedAtMost)

/-- At all valid settings some weights pass the worst-case check. -/
def SomeWeightsPassAtAllValidSettings : Prop :=
  ∀ settings : IntegerTransformer.Settings, settingsAreValid settings = true →
    ∃ weights : ModelWeights settings, PassesWorstCaseCheck settings weights

/-- At all valid settings some weights pass the worst-case check: the weights with 0 at every
place. -/
theorem someWeightsPassAtAllValidSettings : SomeWeightsPassAtAllValidSettings :=
  VerifiableInference.Bounds.exists_passesWorstCaseCheck

/-- **If at all valid settings some weights pass, then at all public files in use some weights
pass**, and completeness at every prompt holds of them. -/
theorem some_weights_pass_at_all_files_in_use (somePass : SomeWeightsPassAtAllValidSettings)
    (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters) :
    ∃ weights : ModelWeights (settingsOfRead parameters),
      PassesWorstCaseCheck (settingsOfRead parameters) weights ∧
      ∀ (prompt : List Token) (length : ℕ), prompt ≠ [] →
        (∀ token ∈ prompt, token < (settingsOfRead parameters).vocabulary) → 0 < length →
        prompt.length + length ≤ 1025 →
        ∃ output : List Token, output.length = length ∧
          IsTheModelsOwnOutput (settingsOfRead parameters) weights prompt output ∧
          (∀ other : List Token, other.length = length →
            IsTheModelsOwnOutput (settingsOfRead parameters) weights prompt other →
              other = output) ∧
          HonestProofRejectedAtMost (finalSystem honestProversAndSettings files (settingsOfRead parameters))
            weights (prompt, output) finalCompletenessError := by
  obtain ⟨weights, passes⟩ := somePass (settingsOfRead parameters) (valid_of_read inUse.read)
  exact ⟨weights, passes, fun prompt length notEmpty inVocabulary positive fits =>
    theHonestPart_complete_where_the_worst_case_check_passes files parameters inUse weights passes
      prompt length notEmpty inVocabulary positive fits⟩

/-- **At all public files in use some weights pass the worst-case check**, and completeness at every
prompt holds of them. -/
theorem at_all_files_in_use_some_weights_pass (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy)
    (inUse : FilesInUse files parameters) :
    ∃ weights : ModelWeights (settingsOfRead parameters),
      PassesWorstCaseCheck (settingsOfRead parameters) weights ∧
      ∀ (prompt : List Token) (length : ℕ), prompt ≠ [] →
        (∀ token ∈ prompt, token < (settingsOfRead parameters).vocabulary) → 0 < length →
        prompt.length + length ≤ 1025 →
        ∃ output : List Token, output.length = length ∧
          IsTheModelsOwnOutput (settingsOfRead parameters) weights prompt output ∧
          (∀ other : List Token, other.length = length →
            IsTheModelsOwnOutput (settingsOfRead parameters) weights prompt other →
              other = output) ∧
          HonestProofRejectedAtMost (finalSystem honestProversAndSettings files (settingsOfRead parameters))
            weights (prompt, output) finalCompletenessError :=
  some_weights_pass_at_all_files_in_use someWeightsPassAtAllValidSettings files parameters inUse

end VerifiableInference.Compilation

#check @VerifiableInference.Compilation.at_all_files_in_use_some_weights_pass
#check @VerifiableInference.Compilation.some_weights_pass_at_all_files_in_use
#print VerifiableInference.Compilation.SomeWeightsPassAtAllValidSettings
#print axioms VerifiableInference.Compilation.some_weights_pass_at_all_files_in_use
#print axioms VerifiableInference.Compilation.at_all_files_in_use_some_weights_pass
