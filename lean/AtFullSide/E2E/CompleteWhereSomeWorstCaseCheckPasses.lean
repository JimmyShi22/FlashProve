-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/CompleteWhereSomeWorstCaseCheckPasses.lean

Completeness of the compiled system at every prompt, for weights that pass the first worst-case
check, or the least-bound check with numbers that hold.

`PassesSomeWorstCaseCheck settings weights` (VerifiableInference/Bounds/SomeWorstCaseCheck.lean)
says: the weights pass the first worst-case check (`PassesWorstCaseCheck`), or there are numbers
that hold and with which they pass the least-bound check. "Hold" (`LeastBoundNumbers.Hold`,
IntegerModel/Bounds/LeastBoundCheck.lean) says of the numbers together, of each stretch bound that
the check reads: it is at least 0, and no vector of whole numbers gets longer by more than that
factor when it is multiplied with its matrix: a matrix of the weights, one value head's columns of
one, or an up matrix with each column scaled by the check's own bound on that unit's activation.
That bound is made from the settings, the tables, the weights, the taus and other numbers: those of
the layers below, and this layer's for the output matrix and the value heads. Nothing is asked of
the taus. No prompt occurs in the premise. At weights that meet it no range condition of the integer
model ever fails (`rangeConditionsNeverFail_of_passesSomeWorstCaseCheck`).
Main statement.
  * `theHonestPart_complete_where_some_worst_case_check_passes`: at all public files in use
    (`FilesInUse`, Johnson/Face/FinalStatement.lean) and all weights that meet
    `PassesSomeWorstCaseCheck`: for every prompt that is not empty and whose tokens are in the
    vocabulary, and every length of at least 1 such that prompt and output have at most 1,025
    tokens, there is an output of that length that is the model's own, it is the only one, and at
    that request the honest proof is rejected with probability at most finalCompletenessError
    (2^-40). It is `theHonestPart_complete_where_rangeConditionsNeverFail`
    (AtFullSide/E2E/CompleteAtEveryPrompt.lean) behind that theorem.
  * `requestLabel_ne_failed_where_some_worst_case_check_passes`: at such weights no request has the
    label `failed` (VerifiableInference/RequestLabel.lean).

It is at least as wide as the statement in AtFullSide/E2E/CompleteWhereTheWorstCaseCheckPasses.lean:
the premise there is the first arm of the premise here. No theorem says that the second arm holds of
any weights of which the first does not.

Limits. `PassesSomeWorstCaseCheck` is no test. Its first arm is one; its second arm says that
numbers exist that hold and pass, which is a statement. So the premise is not said to be decidable.
To pass the least-bound check is not enough: the numbers must hold
(IntegerModel/Bounds/LeastBoundCheckControl.lean has a model without a value that passes with
numbers that do not hold). With numbers in hand the second arm follows from tests alone by two
theorems of VerifiableInference/Bounds/SomeWorstCaseCheck.lean: with numbers that pass the scaled
Gram test, or with the Frobenius numbers. A third carries the length check over, with stretch
numbers that hold. This file shows of no weights that they meet the second arm. At the stored files
AtFullSide/E2E/CompleteAtTheStoredFilesAtWeightsWithin800.lean does; at the example settings
VerifiableInference/Bounds/SomeWeightsPassLengthCheck.lean has weights that pass the length check
with the Frobenius stretch numbers. That some weights meet the first arm is shown in the files that
AtFullSide/E2E/CompleteWhereTheWorstCaseCheckPasses.lean names. What that file's head says under
"What it adds and what it does not" and under "Limits" holds here as well: the statement covers no
request that `FinalComplete` does not already cover; the checks are sufficient, not necessary, and
this library's own; no file says that the converted weights of a real model pass any of them;
nothing in a commitment, in a proof or in what a verifier does shows that the committed weights
pass; the prover is the Lean definition; the statement names weights at which failure does not
occur.
-/
import AtFullSide.E2E.CompleteAtEveryPrompt
import VerifiableInference.Bounds.SomeWorstCaseCheck

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Compilation
open VerifierAndGoals AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm
open VerifiableInference.AtEveryRequest (Request HonestProofRejectedAtMost requestLabel)

/-- **Completeness at every prompt, of the honest part, at weights that pass the first worst-case
check, or the least-bound check with numbers that hold.** -/
theorem theHonestPart_complete_where_some_worst_case_check_passes (files : PublicFiles)
    (parameters : Inst.Model.ScalesAndPolicy) (inUse : FilesInUse files parameters)
    (weights : ModelWeights (settingsOfRead parameters))
    (passes : PassesSomeWorstCaseCheck (settingsOfRead parameters) weights)
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
    (rangeConditionsNeverFail_of_passesSomeWorstCaseCheck (settingsOfRead parameters) weights
      passes)
    prompt length notEmpty inVocabulary positive fits

/-- At weights that pass the first worst-case check, or the least-bound check with numbers that
hold, no request has the label `failed`. -/
theorem requestLabel_ne_failed_where_some_worst_case_check_passes
    {settings : IntegerTransformer.Settings} {weights : ModelWeights settings}
    (passes : PassesSomeWorstCaseCheck settings weights) (request : Request) :
    requestLabel settings weights request ≠ .failed :=
  requestLabel_ne_failed (modelNeverFails_of_passesSomeWorstCaseCheck settings weights passes)
    request

end VerifiableInference.Compilation

#check @VerifiableInference.Compilation.theHonestPart_complete_where_some_worst_case_check_passes
#check @VerifiableInference.Compilation.requestLabel_ne_failed_where_some_worst_case_check_passes
#print VerifiableInference.PassesSomeWorstCaseCheck
#print axioms VerifiableInference.Compilation.theHonestPart_complete_where_some_worst_case_check_passes
#print axioms VerifiableInference.Compilation.requestLabel_ne_failed_where_some_worst_case_check_passes
