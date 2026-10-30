-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/CompleteAtTheStoredFilesAtSmallWeights.lean

Completeness of the compiled system at every prompt, at the stored full-size public files, for a
family of made-up weights, with no hypothesis on the weights but a bound on the entries of their
layers' matrices. Their embedding and their head matrix (`weights.head`: from the last stream to the
logits) are free.

The statement in AtFullSide/E2E/CompleteWhereTheWorstCaseCheckPasses.lean has the premise that the
weights pass the worst-case check. This file shows that the premise can be met at public files in
use: at the stored files `storedPublicFiles`, whose settings are those of the reference table of scales
(`VerifierAndGoals.AtFiles.settingsOfRead_named`, Johnson/Goal/Files/MeetsPolicyAtFiles.lean), all weights
pass whose layers' matrices have every entry in -200 .. 200
(`passesWorstCaseCheck_atReferenceSettings`,
VerifiableInference/Bounds/PassAtReferenceSettings.lean).

* `passesWorstCaseCheck_of_settings_eq`: the same at any settings that equal the reference settings.
* `complete_at_the_stored_files_at_small_weights`: at `storedPublicFiles`, for all such weights, every prompt
  and every length that fit a request: the model's own output of that length exists, is the only
  one, and at that request the honest proof is rejected with probability at most
  finalCompletenessError.

* `storedConstantWeights`, `complete_at_the_stored_files_at_the_constant_weights`: the family has a
  member: the made-up weights with 200 at every place of every matrix. Of them the statement holds
  with no hypothesis at all.

Limits. The named member shows that the family is not empty and holds weights without a zero matrix.
It shows little of the model: all columns of its head matrix are equal, so all logits of a
position are equal; so, ties going to the lowest index, the model's own output is token 0 at every
place (by reading; no theorem here says it). No weights are named here at which a layer computes
something that reaches the answer; such a member of the family is named in
AtFullSide/E2E/CompleteAtTheStoredFilesAtWeightsThatReadAnEarlierToken.lean. The weights are made
up: nothing is said of the converted weights of a real model. One set of public files; at other
files in use the table of scales is free, and nothing here says that any weights pass there (the
weights with 0 at every place do: AtFullSide/E2E/TheWorstCaseCheckCanBeMet.lean). The limits at the
head of AtFullSide/E2E/CompleteWhereTheWorstCaseCheckPasses.lean stand.
-/
import AtFullSide.E2E.CompleteWhereTheWorstCaseCheckPasses
import AtFullSide.CompletenessAndZeroKnowledge.LinesAtStoredFiles
import Johnson.Goal.Files.MeetsPolicyAtFiles
import VerifiableInference.Bounds.PassAtReferenceSettings
import VerifiableInference.Bounds.SomeWeightsPassAtValidSettings

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open IntegerTransformer.Bounds VerifiableInference.Bounds
open VerifiableInference.AtEveryRequest (HonestProofRejectedAtMost)

/-- At settings that equal the reference settings, all weights pass the worst-case check whose
layers' matrices have every entry in -200 .. 200. -/
theorem passesWorstCaseCheck_of_settings_eq {settings : IntegerTransformer.Settings}
    (isReference : settings = referenceSettings) (weights : ModelWeights settings)
    (small : ∀ layer, layer < settings.layers →
      LayerWithin 200 (weights.val.perLayer.entry layer)) :
    PassesWorstCaseCheck settings weights := by
  subst isReference
  exact passesWorstCaseCheck_atReferenceSettings weights small

/-- **Completeness at every prompt, at the stored files, for all weights with small entries.** -/
theorem complete_at_the_stored_files_at_small_weights
    (weights : ModelWeights (settingsOfRead storedParameters))
    (small : ∀ layer, layer < (settingsOfRead storedParameters).layers →
      LayerWithin 200 (weights.val.perLayer.entry layer))
    (prompt : List Token) (length : ℕ) (notEmpty : prompt ≠ [])
    (inVocabulary : ∀ token ∈ prompt, token < (settingsOfRead storedParameters).vocabulary)
    (positive : 0 < length) (fits : prompt.length + length ≤ 1025) :
    ∃ output : List Token, output.length = length ∧
      IsTheModelsOwnOutput (settingsOfRead storedParameters) weights prompt output ∧
      (∀ other : List Token, other.length = length →
        IsTheModelsOwnOutput (settingsOfRead storedParameters) weights prompt other →
          other = output) ∧
      HonestProofRejectedAtMost (finalSystem honestProversAndSettings storedPublicFiles (settingsOfRead storedParameters))
        weights (prompt, output) finalCompletenessError :=
  theHonestPart_complete_where_the_worst_case_check_passes storedPublicFiles storedParameters filesInUse_stored
    weights
    (passesWorstCaseCheck_of_settings_eq
      (VerifierAndGoals.AtFiles.settingsOfRead_named (Or.inl rfl) filesInUse_stored.read) weights small)
    prompt length notEmpty inVocabulary positive fits

/-- Made-up weights at the settings of the stored files: every entry of every matrix is 200. -/
def storedConstantWeights : ModelWeights (settingsOfRead storedParameters) :=
  ⟨constantWeights (settingsOfRead storedParameters) 200,
    weightsAreValid_constantWeights_of_settingsAreValid (settingsOfRead storedParameters)
      (valid_of_read filesInUse_stored.read) 200 (by decide) (by decide)⟩

/-- Their layers' matrices have every entry in -200 .. 200. -/
theorem storedConstantWeights_small (layer : ℕ)
    (inLayers : layer < (settingsOfRead storedParameters).layers) :
    LayerWithin 200 (storedConstantWeights.val.perLayer.entry layer) := by
  show LayerWithin 200
    ((constantWeights (settingsOfRead storedParameters) 200).perLayer.entry layer)
  rw [constantWeights_layer _ _ layer inLayers]
  exact layerWithin_constantLayer _ _ _ _ (by decide)

/-- **Completeness at every prompt, at the stored files and the constant weights**: no hypothesis is
left. -/
theorem complete_at_the_stored_files_at_the_constant_weights
    (prompt : List Token) (length : ℕ) (notEmpty : prompt ≠ [])
    (inVocabulary : ∀ token ∈ prompt, token < (settingsOfRead storedParameters).vocabulary)
    (positive : 0 < length) (fits : prompt.length + length ≤ 1025) :
    ∃ output : List Token, output.length = length ∧
      IsTheModelsOwnOutput (settingsOfRead storedParameters) storedConstantWeights prompt output ∧
      (∀ other : List Token, other.length = length →
        IsTheModelsOwnOutput (settingsOfRead storedParameters) storedConstantWeights prompt other →
          other = output) ∧
      HonestProofRejectedAtMost (finalSystem honestProversAndSettings storedPublicFiles (settingsOfRead storedParameters))
        storedConstantWeights (prompt, output) finalCompletenessError :=
  complete_at_the_stored_files_at_small_weights storedConstantWeights storedConstantWeights_small
    prompt length notEmpty inVocabulary positive fits

end VerifiableInference.Compilation

#check @VerifiableInference.Compilation.complete_at_the_stored_files_at_the_constant_weights
#check @VerifiableInference.Compilation.complete_at_the_stored_files_at_small_weights
#print axioms VerifiableInference.Compilation.complete_at_the_stored_files_at_small_weights
#print axioms VerifiableInference.Compilation.complete_at_the_stored_files_at_the_constant_weights
