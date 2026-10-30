-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/CompleteAtTheStoredFilesAtWeightsWithin800.lean

Completeness of the compiled system at every prompt, at the stored full-size public files, for all
weights whose layers' matrices have every entry in -800 .. 800.

The premise of the statement in AtFullSide/E2E/CompleteWhereSomeWorstCaseCheckPasses.lean can be met
at public files in use, and so can its second arm. At the reference settings all such weights pass
the length check with the Frobenius stretch numbers, which hold
(VerifiableInference/Bounds/PassLengthCheckAtReferenceSettings.lean), and the stored files read as
the reference settings (`settingsOfRead_named`, Johnson/Goal/Files/MeetsPolicyAtFiles.lean).

* `secondArm_of_settings_eq`, `secondArm_at_the_stored_files`: at settings that equal the reference
  settings, and so at the stored files, for all weights whose layers' matrices have every entry in
  -800 .. 800 there are numbers that hold and with which the weights pass the least-bound check: the
  second arm of `PassesSomeWorstCaseCheck`, as a statement of its own.
* `passesSomeWorstCaseCheck_of_settings_eq`: at settings that equal the reference settings, all
  weights whose layers' matrices have every entry in -800 .. 800 meet `PassesSomeWorstCaseCheck`.
* `complete_at_the_stored_files_at_weights_within_800`: at the stored files and all such weights,
  for every prompt and every length that fit a request, the model's own output of that length
  exists, is the only one, and at that request the honest proof is rejected with probability at most
  finalCompletenessError. Their embedding and their head matrix (`weights.head`: from the last
  stream to the logits) are free.
* `storedWeightsOf800`, `complete_at_the_stored_files_at_the_weights_of_800`: the family has a
  member: the made-up weights with 800 at every place of every matrix. Of them the statement holds
  with no hypothesis at all.

Limits. The bound 800 is chosen so that the test passes; nothing says that the converted weights of
a real model lie within it. The named member shows that the family is not empty. It shows little of
the model: all columns of its head matrix are equal, so all logits of a position are equal; so, ties
going to the lowest index, the model's own output is token 0 at every place (by reading; no theorem
here says it). By their definition the weights of
AtFullSide/E2E/CompleteAtTheStoredFilesAtWeightsThatReadAnEarlierToken.lean lie in the family too:
their layers' matrices lie in -200 .. 200, and at them the answer depends on an earlier token. No
theorem here says that these weights do not pass the first worst-case check as well. One set of
public files; at other files in use the table of scales is free, and nothing here says that any
weights meet the second arm there. The limits at the head of
AtFullSide/E2E/CompleteWhereSomeWorstCaseCheckPasses.lean stand.
-/
import AtFullSide.E2E.CompleteWhereSomeWorstCaseCheckPasses
import AtFullSide.CompletenessAndZeroKnowledge.LinesAtStoredFiles
import Johnson.Goal.Files.MeetsPolicyAtFiles
import VerifiableInference.Bounds.PassLengthCheckAtReferenceSettings
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

/-- **The second arm, as a statement.** At settings that equal the reference settings, for all
weights whose layers' matrices have every entry in -800 .. 800 there are numbers that hold and with
which the weights pass the least-bound check. The proof takes the numbers that match the Frobenius
stretch numbers. -/
theorem secondArm_of_settings_eq {settings : IntegerTransformer.Settings}
    (isReference : settings = referenceSettings) (weights : ModelWeights settings)
    (small : ∀ layer, layer < settings.layers →
      LayerWithin 800 (weights.val.perLayer.entry layer)) :
    ∃ numbers : LeastBoundNumbers, numbers.Hold settings lookupTables weights.val ∧
      PassesLeastBoundWorstCaseCheck settings weights numbers := by
  subst isReference
  have holds := frobeniusStretchNumbers_hold referenceSettings weights.val
  exact ⟨leastBoundNumbersOf referenceSettings lookupTables weights.val []
      (frobeniusStretchNumbers referenceSettings weights.val),
    leastBoundNumbersOf_hold referenceSettings lookupTables weights.val [] _ holds,
    leastBoundWorstCaseCheck_of_lengthWorstCaseCheck referenceSettings lookupTables weights.val []
      _ (nonNegative_of_hold referenceSettings weights.val _ holds)
      (passesFrobeniusLengthCheck_atReferenceSettings weights small)⟩

/-- The second arm at the stored files. -/
theorem secondArm_at_the_stored_files (weights : ModelWeights (settingsOfRead storedParameters))
    (small : ∀ layer, layer < (settingsOfRead storedParameters).layers →
      LayerWithin 800 (weights.val.perLayer.entry layer)) :
    ∃ numbers : LeastBoundNumbers,
      numbers.Hold (settingsOfRead storedParameters) lookupTables weights.val ∧
      PassesLeastBoundWorstCaseCheck (settingsOfRead storedParameters) weights numbers :=
  secondArm_of_settings_eq
    (VerifierAndGoals.AtFiles.settingsOfRead_named (Or.inl rfl) filesInUse_stored.read) weights small

/-- At settings that equal the reference settings, all weights whose layers' matrices have every
entry in -800 .. 800 pass the first worst-case check, or the least-bound check with numbers that
hold. -/
theorem passesSomeWorstCaseCheck_of_settings_eq {settings : IntegerTransformer.Settings}
    (isReference : settings = referenceSettings) (weights : ModelWeights settings)
    (small : ∀ layer, layer < settings.layers →
      LayerWithin 800 (weights.val.perLayer.entry layer)) :
    PassesSomeWorstCaseCheck settings weights := by
  subst isReference
  exact passesSomeWorstCaseCheck_atReferenceSettings weights small

/-- **Completeness at every prompt, at the stored files, for all weights whose layers' matrices have
every entry in -800 .. 800.** -/
theorem complete_at_the_stored_files_at_weights_within_800
    (weights : ModelWeights (settingsOfRead storedParameters))
    (small : ∀ layer, layer < (settingsOfRead storedParameters).layers →
      LayerWithin 800 (weights.val.perLayer.entry layer))
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
  theHonestPart_complete_where_some_worst_case_check_passes storedPublicFiles storedParameters
    filesInUse_stored weights
    (passesSomeWorstCaseCheck_of_settings_eq
      (VerifierAndGoals.AtFiles.settingsOfRead_named (Or.inl rfl) filesInUse_stored.read) weights small)
    prompt length notEmpty inVocabulary positive fits

/-- Made-up weights at the settings of the stored files: every entry of every matrix is 800. -/
def storedWeightsOf800 : ModelWeights (settingsOfRead storedParameters) :=
  ⟨constantWeights (settingsOfRead storedParameters) 800,
    weightsAreValid_constantWeights_of_settingsAreValid (settingsOfRead storedParameters)
      (valid_of_read filesInUse_stored.read) 800 (by decide) (by decide)⟩

/-- Their layers' matrices have every entry in -800 .. 800. -/
theorem storedWeightsOf800_small (layer : ℕ)
    (inLayers : layer < (settingsOfRead storedParameters).layers) :
    LayerWithin 800 (storedWeightsOf800.val.perLayer.entry layer) := by
  show LayerWithin 800
    ((constantWeights (settingsOfRead storedParameters) 800).perLayer.entry layer)
  rw [constantWeights_layer _ _ layer inLayers]
  exact layerWithin_constantLayer _ _ _ _ (by decide)

/-- **Completeness at every prompt, at the stored files and the weights with 800 at every place**:
no hypothesis is left. -/
theorem complete_at_the_stored_files_at_the_weights_of_800
    (prompt : List Token) (length : ℕ) (notEmpty : prompt ≠ [])
    (inVocabulary : ∀ token ∈ prompt, token < (settingsOfRead storedParameters).vocabulary)
    (positive : 0 < length) (fits : prompt.length + length ≤ 1025) :
    ∃ output : List Token, output.length = length ∧
      IsTheModelsOwnOutput (settingsOfRead storedParameters) storedWeightsOf800 prompt output ∧
      (∀ other : List Token, other.length = length →
        IsTheModelsOwnOutput (settingsOfRead storedParameters) storedWeightsOf800 prompt other →
          other = output) ∧
      HonestProofRejectedAtMost (finalSystem honestProversAndSettings storedPublicFiles (settingsOfRead storedParameters))
        storedWeightsOf800 (prompt, output) finalCompletenessError :=
  complete_at_the_stored_files_at_weights_within_800 storedWeightsOf800 storedWeightsOf800_small
    prompt length notEmpty inVocabulary positive fits

end VerifiableInference.Compilation

#check @VerifiableInference.Compilation.secondArm_at_the_stored_files
#check @VerifiableInference.Compilation.complete_at_the_stored_files_at_weights_within_800
#check @VerifiableInference.Compilation.complete_at_the_stored_files_at_the_weights_of_800
#print axioms VerifiableInference.Compilation.secondArm_at_the_stored_files
#print axioms VerifiableInference.Compilation.passesSomeWorstCaseCheck_of_settings_eq
#print axioms VerifiableInference.Compilation.complete_at_the_stored_files_at_weights_within_800
#print axioms VerifiableInference.Compilation.complete_at_the_stored_files_at_the_weights_of_800
