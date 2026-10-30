-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/CompleteAtTheStoredFilesAtWeightsThatReadAnEarlierToken.lean

Completeness of the compiled system at every prompt, at the stored full-size public files, at
made-up weights at which the model's answer depends on an earlier token.

The family of AtFullSide/E2E/CompleteAtTheStoredFilesAtSmallWeights.lean (every matrix of every
layer has every entry in -200 .. 200) has a member at which a layer computes something that reaches
the answer: `markingWeights` (VerifiableInference/Bounds/PassingWeightsTellPromptsApart.lean), at
the stored files' own settings.

* `storedMarkingWeights`: these weights, valid at the stored files' settings.
* `storedMarkingWeights_pass`: they pass the worst-case check.
* `storedMarkingWeights_read_an_earlier_token`: the prompts `[0, 1]` and `[1, 1]` end in the same
  token, and the model answers with 1 and with 0.
* `complete_at_the_stored_files_at_the_marking_weights`: at these weights, for every
  prompt and every length that fit a request, the model's own output of that length exists, is the
  only one, and at that request the honest proof is rejected with probability at most
  finalCompletenessError. No hypothesis is left.

Limits. The weights are made up: nothing is said of the converted weights of a real model. One
attention layer takes a plain mean; that an earlier token matters is stated on two prompts of two
tokens; no feed-forward block, router, rotary step or score takes part, and no layer above the
first. One set of public files. The limits at the heads of
AtFullSide/E2E/CompleteAtTheStoredFilesAtSmallWeights.lean and
AtFullSide/E2E/CompleteWhereTheWorstCaseCheckPasses.lean stand.
-/
import AtFullSide.E2E.CompleteAtTheStoredFilesAtSmallWeights
import VerifiableInference.Bounds.TheMarkAtReferenceSettings

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

/-- At settings that equal the reference settings the mark survives. -/
theorem markedEntry_of_settings_eq {settings : IntegerTransformer.Settings}
    (isReference : settings = referenceSettings) :
    0 < normOfOneEntry settings.finalBits settings.finalShift settings.finalEps
      (markedEntry settings 0 1) ∧
    normOfOneEntry settings.finalBits settings.finalShift settings.finalEps
      (markedEntry settings 1 1) = 0 := by
  subst isReference
  exact markedEntry_referenceSettings

/-- The marking weights at the settings of the stored files. -/
def storedMarkingWeights : ModelWeights (settingsOfRead storedParameters) :=
  markingWeightsAt (settingsOfRead storedParameters) (valid_of_read filesInUse_stored.read)

/-- They pass the worst-case check. -/
theorem storedMarkingWeights_pass :
    PassesWorstCaseCheck (settingsOfRead storedParameters) storedMarkingWeights :=
  passesWorstCaseCheck_of_settings_eq
    (VerifierAndGoals.AtFiles.settingsOfRead_named (Or.inl rfl) filesInUse_stored.read) storedMarkingWeights
    (markingWeightsAt_small _ _)

/-- **At these weights an earlier token matters**: the prompts `[0, 1]` and `[1, 1]` end in the same
token, and the model answers with 1 and with 0. -/
theorem storedMarkingWeights_read_an_earlier_token :
    modelNextToken (settingsOfRead storedParameters) storedMarkingWeights [0, 1] = some 1 ∧
      modelNextToken (settingsOfRead storedParameters) storedMarkingWeights [1, 1] = some 0 :=
  modelNextToken_markingWeightsAt_apart _ _
    (rangeConditionsNeverFail_of_passesWorstCaseCheck _ _ storedMarkingWeights_pass)
    (markedEntry_of_settings_eq
      (VerifierAndGoals.AtFiles.settingsOfRead_named (Or.inl rfl) filesInUse_stored.read)).1
    (markedEntry_of_settings_eq
      (VerifierAndGoals.AtFiles.settingsOfRead_named (Or.inl rfl) filesInUse_stored.read)).2

/-- **Completeness at every prompt, at the stored files, at weights that read an earlier token**: no
hypothesis is left. -/
theorem complete_at_the_stored_files_at_the_marking_weights
    (prompt : List Token) (length : ℕ) (notEmpty : prompt ≠ [])
    (inVocabulary : ∀ token ∈ prompt, token < (settingsOfRead storedParameters).vocabulary)
    (positive : 0 < length) (fits : prompt.length + length ≤ 1025) :
    ∃ output : List Token, output.length = length ∧
      IsTheModelsOwnOutput (settingsOfRead storedParameters) storedMarkingWeights prompt output ∧
      (∀ other : List Token, other.length = length →
        IsTheModelsOwnOutput (settingsOfRead storedParameters) storedMarkingWeights prompt other →
          other = output) ∧
      HonestProofRejectedAtMost (finalSystem honestProversAndSettings storedPublicFiles (settingsOfRead storedParameters))
        storedMarkingWeights (prompt, output) finalCompletenessError :=
  theHonestPart_complete_where_the_worst_case_check_passes storedPublicFiles storedParameters filesInUse_stored
    storedMarkingWeights storedMarkingWeights_pass prompt length notEmpty inVocabulary positive fits

end VerifiableInference.Compilation

#check @VerifiableInference.Compilation.storedMarkingWeights_read_an_earlier_token
#check @VerifiableInference.Compilation.complete_at_the_stored_files_at_the_marking_weights
#print axioms VerifiableInference.Compilation.storedMarkingWeights_pass
#print axioms VerifiableInference.Compilation.storedMarkingWeights_read_an_earlier_token
#print axioms VerifiableInference.Compilation.complete_at_the_stored_files_at_the_marking_weights
