-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/CompleteWhereTheWorstCaseCheckPasses.lean

Completeness of the compiled system at every prompt, for weights that pass a worst-case check.

`PassesWorstCaseCheck settings weights` (VerifiableInference/Bounds/NeverFails.lean) says that a
Boolean function of the settings, the system's five tables and the weights has the value true. It
reads no prompt. At weights that pass it no range condition of the integer model ever fails
(`rangeConditionsNeverFail_of_passesWorstCaseCheck`, the same file).

Main statement.
  * `theHonestPart_complete_where_the_worst_case_check_passes`: at all public files in use
    (`FilesInUse`, Johnson/Face/FinalStatement.lean) and all weights that pass the check: for every
    prompt that is not empty and whose tokens are in the vocabulary, and every length of at least 1
    such that prompt and output have at most 1,025 tokens, there is an output of that length that is
    the model's own, it is the only one, and at that request the honest proof is rejected with
    probability at most finalCompletenessError (2^-40). It is
    `theHonestPart_complete_where_rangeConditionsNeverFail`
    (AtFullSide/E2E/CompleteAtEveryPrompt.lean) behind that theorem.
  * `requestLabel_ne_failed_where_the_worst_case_check_passes`: at such weights no request has the
    label `failed` (VerifiableInference/RequestLabel.lean).

What it adds and what it does not. The main statement covers no request that the line on
completeness in the final statement (`FinalComplete`, Johnson/Face/FinalStatement.lean) does not
already cover: that line holds at all weights, for every well-formed request whose claimed output is
the model's result. What the check adds is that such a request exists at every prompt and every
output length that fits: every prompt, not every request. (That its output is the model's own, and
the only one of its length, holds at any weights.) Of a request that claims other tokens neither
statement says anything.

Limits. This file shows of no weights that they pass the check. That some weights pass is shown at
all public files in use for weights with 0 at every place
(AtFullSide/E2E/TheWorstCaseCheckCanBeMet.lean), and at the stored files alone for all weights whose
layers' matrices have every entry in -200 .. 200
(AtFullSide/E2E/CompleteAtTheStoredFilesAtSmallWeights.lean), among them weights at which the answer
depends on an earlier token
(AtFullSide/E2E/CompleteAtTheStoredFilesAtWeightsThatReadAnEarlierToken.lean). The weights that are
named are made up.
The check is sufficient, not necessary: weights that do not pass may still never fail. It is
decidable, but at the full sizes of the weights it cannot in practice be evaluated as it is written
(the head of IntegerModel/Bounds/Check.lean). The statement is for whoever holds the weights:
nothing in a commitment, in a proof or in what a verifier does shows that the committed weights
pass. It is this library's own check: no theorem here relates it to a check that any program makes,
and no file says that the converted weights of a real model pass it. The prover is the Lean
definition; nothing is said of the programs. The statement does not make completeness hold where
the model's result is failure: it names weights at which failure does not occur. The other limits
at the heads of AtFullSide/E2E/CompleteAtEveryPrompt.lean and IntegerModel/Bounds/Check.lean stand.
-/
import AtFullSide.E2E.CompleteAtEveryPrompt
import VerifiableInference.Bounds.NeverFails

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open VerifiableInference.AtEveryRequest (Request HonestProofRejectedAtMost requestLabel)

/-- **Completeness at every prompt, of the honest part, at weights that pass the worst-case
check.** -/
theorem theHonestPart_complete_where_the_worst_case_check_passes (files : PublicFiles)
    (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters)
    (weights : ModelWeights (settingsOfRead parameters))
    (passes : PassesWorstCaseCheck (settingsOfRead parameters) weights)
    (prompt : List Token) (length : ℕ) (notEmpty : prompt ≠ [])
    (inVocabulary : ∀ token ∈ prompt, token < (settingsOfRead parameters).vocabulary)
    (positive : 0 < length) (fits : prompt.length + length ≤ 1025) :
    ∃ output : List Token, output.length = length ∧
      IsTheModelsOwnOutput (settingsOfRead parameters) weights prompt output ∧
      (∀ other : List Token, other.length = length →
        IsTheModelsOwnOutput (settingsOfRead parameters) weights prompt other → other = output) ∧
      HonestProofRejectedAtMost (finalSystem honestProversAndSettings files (settingsOfRead parameters))
        weights (prompt, output) finalCompletenessError :=
  theHonestPart_complete_where_rangeConditionsNeverFail files parameters inUse weights
    (rangeConditionsNeverFail_of_passesWorstCaseCheck (settingsOfRead parameters) weights passes)
    prompt length notEmpty inVocabulary positive fits

/-- At weights that pass the worst-case check no request has the label `failed`. -/
theorem requestLabel_ne_failed_where_the_worst_case_check_passes
    {settings : IntegerTransformer.Settings} {weights : ModelWeights settings}
    (passes : PassesWorstCaseCheck settings weights) (request : Request) :
    requestLabel settings weights request ≠ .failed :=
  requestLabel_ne_failed (modelNeverFails_of_passesWorstCaseCheck settings weights passes) request

end VerifiableInference.Compilation

#check @VerifiableInference.Compilation.theHonestPart_complete_where_the_worst_case_check_passes
#print VerifiableInference.PassesWorstCaseCheck
#print axioms VerifiableInference.Compilation.theHonestPart_complete_where_the_worst_case_check_passes
#print axioms VerifiableInference.Compilation.requestLabel_ne_failed_where_the_worst_case_check_passes
