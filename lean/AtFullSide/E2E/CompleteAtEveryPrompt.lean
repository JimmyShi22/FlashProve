-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/CompleteAtEveryPrompt.lean

Completeness of the compiled system at every prompt, for weights at which the model's own output
exists. It states no goal: its statements are steps toward the one in
AtFullSide/E2E/CompleteWhereTheWorstCaseCheckPasses.lean.

The line on completeness in the final statement, `FinalComplete` (Johnson/Face/FinalStatement.lean),
speaks of a well-formed request only if the model's result on it is the claimed output. The integer
model is partial, so at some weights and prompts no output has that property, and there the line
says nothing. This file carries the line to every prompt at weights at which that does not happen.
That it does not happen is the hypothesis `TheModelsOwnOutputExists`. So the general statement here
adds to `FinalComplete` what it assumes; what it is for is the two sufficient conditions:
`RangeConditionsNeverFail` here, and a decidable check in
AtFullSide/E2E/CompleteWhereTheWorstCaseCheckPasses.lean.

Terms.
  * Public files are "in use" when `FilesInUse files parameters` holds: they are in scope, they read
    as these parameters, their policy is exact match, and they pass the verifier's first test on
    public files.
  * `TheModelsOwnOutputExists settings weights` (VerifiableInference/TheModelsOwnOutput.lean): for
    every prompt and every length that fit a request there is an output of that length whose request
    has that output as its result.
  * `IsTheModelsOwnOutput` (the same file): each output token is the model's next token after the
    prompt and the output tokens before it.
  * `HonestProofRejectedAtMost system weights request error` (the same file): with the honest
    committer and prover, the verifier rejects with probability at most error, over a hash function
    drawn at random and the honest side's coins.

Main statements.
  * `CompleteAtEveryPromptAtFiles`, `FinalCompleteAtEveryPrompt`: at all public files in use and all
    weights that meet `TheModelsOwnOutputExists`: for every prompt that is not empty and whose
    tokens are in the vocabulary, and every length of at least 1 such that prompt and output have at
    most 1,025 tokens, there is an output of that length that is the model's own, it is the only
    one, and at that request the honest proof is rejected with probability at most
    finalCompletenessError (2^-40). With 1,025 tokens the last output token lies outside the window
    of 1,024 on which the model is run, and is only compared with the run's choice at the last
    position.
  * `finalCompleteAtEveryPrompt_of_finalComplete`: it follows from `FinalComplete`, for every honest
    part.
  * `theHonestPart_completeAtEveryPrompt`: it holds of `honestProversAndSettings`
    (AtFullSide/Face/HonestProversAndSettingsValue.lean), by `finalAtT1_filled`
    (AtFullSide/E2E/TheCompiledStepFilled.lean).
  * `theHonestPart_complete_where_rangeConditionsNeverFail`: so, at all public files in use and all
    weights at which no range condition of the integer model ever fails (`RangeConditionsNeverFail`,
    VerifiableInference/ModelNeverFails.lean), the same conclusion holds of `honestProversAndSettings`.
  * `complete_at_own_outputs`: at weights that meet `ModelNeverFails`
    (VerifiableInference/ModelNeverFails.lean), at every well-formed request whose output is the
    model's own, the same bound holds.

Limits. `TheModelsOwnOutputExists`, `RangeConditionsNeverFail` and `ModelNeverFails` are hypotheses.
This file shows of no weights that they meet any of them; that they can fail is shown in
VerifiableInference/TheModelsOwnOutputCanFail.lean. The limits of `FinalComplete` stand: one
commitment and one request, the exact-match policy, the random-oracle model. The prover is the Lean
definition; nothing is said of the programs. Nothing is said of a request whose claimed output is
not the model's own. These statements do not make completeness hold where the model's result is
failure: they name weights at which failure does not occur.
-/
import AtFullSide.E2E.TheCompiledStepFilled
import AtFullSide.Face.HonestProversAndSettingsValue
import VerifiableInference.TheModelsOwnOutputFromRangeConditions

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open VerifiableInference.AtEveryRequest (Request WellFormedRequest HonestProofRejectedAtMost)

/-- Completeness at every prompt, at given files. -/
def CompleteAtEveryPromptAtFiles (honest : HonestProversAndSettings) (files : PublicFiles)
    (parameters : Inst.Model.ScalesAndPolicy) : Prop :=
  ∀ weights : ModelWeights (settingsOfRead parameters),
    TheModelsOwnOutputExists (settingsOfRead parameters) weights →
    ∀ (prompt : List Token) (length : ℕ), prompt ≠ [] →
      (∀ token ∈ prompt, token < (settingsOfRead parameters).vocabulary) → 0 < length →
      prompt.length + length ≤ 1025 →
      ∃ output : List Token, output.length = length ∧
        IsTheModelsOwnOutput (settingsOfRead parameters) weights prompt output ∧
        (∀ other : List Token, other.length = length →
          IsTheModelsOwnOutput (settingsOfRead parameters) weights prompt other → other = output) ∧
        HonestProofRejectedAtMost (finalSystem honest files (settingsOfRead parameters)) weights
          (prompt, output) finalCompletenessError

/-- **Completeness at every prompt**, for weights at which the model's own output exists. -/
def FinalCompleteAtEveryPrompt (honest : HonestProversAndSettings) : Prop :=
  ∀ (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy), FilesInUse files parameters →
    CompleteAtEveryPromptAtFiles honest files parameters

/-- **It follows from the final statement's line on completeness**, for every honest part. -/
theorem finalCompleteAtEveryPrompt_of_finalComplete {honest : HonestProversAndSettings}
    (complete : FinalComplete honest) : FinalCompleteAtEveryPrompt honest := by
  intro files parameters inUse weights ownExists prompt length notEmpty inVocabulary positive fits
  obtain ⟨output, isLength, form, result⟩ :=
    ownExists prompt length notEmpty inVocabulary positive fits
  have own := own_output_of_result (valid_of_read inUse.read) form result
  exact ⟨output, isLength, own,
    fun other otherLength otherIsOwn =>
      theModelsOwnOutput_unique (otherLength.trans isLength.symm) otherIsOwn own,
    complete files parameters inUse weights (prompt, output) form result⟩

/-- **Completeness at every prompt, of the honest part.** -/
theorem theHonestPart_completeAtEveryPrompt : FinalCompleteAtEveryPrompt honestProversAndSettings :=
  finalCompleteAtEveryPrompt_of_finalComplete finalAtT1_filled.1.1

/-- **Completeness at every prompt, of the honest part, where no range condition ever fails.** At
all public files in use and all weights at which no range condition of the integer model ever fails:
for every prompt and every length that fit a request there is an output of that length that is the
model's own, it is the only one, and at that request the honest proof is rejected with probability
at most finalCompletenessError. -/
theorem theHonestPart_complete_where_rangeConditionsNeverFail (files : PublicFiles)
    (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters)
    (weights : ModelWeights (settingsOfRead parameters))
    (never : RangeConditionsNeverFail (settingsOfRead parameters) weights)
    (prompt : List Token) (length : ℕ) (notEmpty : prompt ≠ [])
    (inVocabulary : ∀ token ∈ prompt, token < (settingsOfRead parameters).vocabulary)
    (positive : 0 < length) (fits : prompt.length + length ≤ 1025) :
    ∃ output : List Token, output.length = length ∧
      IsTheModelsOwnOutput (settingsOfRead parameters) weights prompt output ∧
      (∀ other : List Token, other.length = length →
        IsTheModelsOwnOutput (settingsOfRead parameters) weights prompt other → other = output) ∧
      HonestProofRejectedAtMost (finalSystem honestProversAndSettings files (settingsOfRead parameters))
        weights (prompt, output) finalCompletenessError :=
  theHonestPart_completeAtEveryPrompt files parameters inUse weights
    (theModelsOwnOutputExists_of_rangeConditionsNeverFail (valid_of_read inUse.read) never)
    prompt length notEmpty inVocabulary positive fits

/-- At weights at which the model never fails: at every well-formed request whose output is the
model's own, the honest proof is rejected with probability at most finalCompletenessError. -/
theorem complete_at_own_outputs {honest : HonestProversAndSettings} (complete : FinalComplete honest)
    (files : PublicFiles) (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters)
    (weights : ModelWeights (settingsOfRead parameters))
    (never : ModelNeverFails (settingsOfRead parameters) weights) (request : Request)
    (wellFormed : WellFormedRequest (settingsOfRead parameters) request)
    (own : IsTheModelsOwnOutput (settingsOfRead parameters) weights request.1 request.2) :
    HonestProofRejectedAtMost (finalSystem honest files (settingsOfRead parameters)) weights
      request finalCompletenessError :=
  complete files parameters inUse weights request wellFormed
    (result_of_own_output (valid_of_read inUse.read) never wellFormed own)

end VerifiableInference.Compilation

#check @VerifiableInference.Compilation.theHonestPart_completeAtEveryPrompt
#check @VerifiableInference.Compilation.theHonestPart_complete_where_rangeConditionsNeverFail
#check @VerifiableInference.Compilation.complete_at_own_outputs
#print VerifiableInference.Compilation.CompleteAtEveryPromptAtFiles
#print VerifiableInference.Compilation.FinalCompleteAtEveryPrompt
#print VerifiableInference.TheModelsOwnOutputExists
#print VerifiableInference.IsTheModelsOwnOutput
#print VerifiableInference.RangeConditionsNeverFail
#print VerifiableInference.AtEveryRequest.HonestProofRejectedAtMost
#print axioms VerifiableInference.Compilation.finalCompleteAtEveryPrompt_of_finalComplete
#print axioms VerifiableInference.Compilation.theHonestPart_completeAtEveryPrompt
#print axioms VerifiableInference.Compilation.theHonestPart_complete_where_rangeConditionsNeverFail
#print axioms VerifiableInference.Compilation.complete_at_own_outputs
