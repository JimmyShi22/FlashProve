-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/RequestResult.lean

What the integer model gives when it is run on a request, a prompt with a claimed output: the
tokens that the run chooses for the output's positions, or failure if the model has no value.

A request is a prompt together with a claimed output, in the form that `RequestForm` states. The
integer model is partial: it has no value on a list of tokens if a range condition fails at one of
their positions. `requestResult` runs the model on the request's whole window of 1,024 tokens
(`IntegerModel.zeroFilledWindow`). If the model has no value there, the result is failure, `none`.
Otherwise the result is the list of the tokens that the run chooses for the positions of the output.

Two definitions and two theorems, over CanServe.lean.
* `RequestForm`: a prompt and output tokens make a request. It does not read the weights.
* `requestResult`: the result.
* `requestResult_isSome_iff`: the result is not failure exactly if the third condition of
  `CanServe` holds.
* `canServe_iff_requestResult`: `CanServe` is its first two conditions and "the result is not
  failure".

At valid settings the output tokens are the model's, and `CanServe` holds, exactly if the prompt and
the output make a request whose result is these output tokens:
`canServe_and_modelOutput_iff`, IntegerModel/Arrays/RequestResultLaws.lean.
-/
import VerifiableInference.CanServe

set_option autoImplicit false

namespace VerifiableInference

open IntegerTransformer

/-- A prompt and output tokens make a request: every token is in the vocabulary, neither list is
empty, and together they have at most 1,025 tokens, one more than the window has positions. The
weights are not read.
The window on which `requestResult` runs the model (`IntegerModel.zeroFilledWindow`) has 1,024
positions. With 1,025 tokens the last output token lies outside the window: the run does not read
it, and it is only compared with the run's choice at the last position.
In `canServe_and_modelOutput_iff` the condition that the prompt is not empty cannot be left out:
`requestResult_of_emptyPrompt` (both in IntegerModel/Arrays/RequestResultLaws.lean).
At valid settings these are the conditions under which `requestOfTokens`
(VerifiableInference/RequestOfTokens.lean) builds the request that the verifier checks
(`requestForm_iff_requestOfTokens`, IntegerModel/Arrays/RequestResultLaws.lean). -/
def RequestForm (settings : Settings) (prompt output : List Nat) : Prop :=
  (∀ token ∈ prompt ++ output, token < settings.vocabulary) ∧ output ≠ [] ∧ prompt ≠ [] ∧
    prompt.length + output.length ≤ 1025

/-- **The model's result on a request.** A request is a prompt with a claimed output that meet
`RequestForm`; the definition takes any two lists. The model is run on the window of 1,024 tokens:
the prompt, the claimed output tokens, then token 0 as often as needed, cut at 1,024 tokens.
`none` is failure: the model has no value on the window. At valid settings that means that a token
of the window is outside the vocabulary, or that a range condition fails at some position of the
window (see `modelNextToken`, VerifiableInference/ModelWeights.lean).
Otherwise the result is `some` of the tokens that the run chooses at the positions just before the
output tokens: position `prompt.length - 1`, at which the last token of the prompt stands, for the
first output token, and so on (for an empty prompt this is position 0, and the list is not aligned
with the output: `requestResult_of_emptyPrompt`, IntegerModel/Arrays/RequestResultLaws.lean). The
run has a choice at each of its 1,024 positions and at no other: where the output reaches further,
the list is shorter than the output.
The result depends on the output tokens, since the run reads those that lie in the window: it is a
function of the prompt and the claimed output, not of the prompt alone. It has three outcomes:
failure; `some` of these output tokens; `some` of other tokens. At valid settings, for a prompt and
output that make a request (`RequestForm`), the output tokens are the model's, each being the
model's next token after the prompt and the output tokens before it, and `CanServe` holds, exactly
in the second case (`canServe_and_modelOutput_iff`, IntegerModel/Arrays/RequestResultLaws.lean). -/
def requestResult (settings : Settings) (weights : ModelWeights settings)
    (prompt output : List Nat) : Option (List Nat) :=
  let window := IntegerModel.zeroFilledWindow prompt output
  if (modelNextToken settings weights window).isSome then
    let choices := (trace settings lookupTables weights.val window.toArray).choices.toList
    some ((choices.drop (prompt.length - 1)).take output.length)
  else none

/-- The result is not failure exactly if the model has a value on the whole window: the third
condition of `CanServe`. -/
theorem requestResult_isSome_iff (settings : Settings) (weights : ModelWeights settings)
    (prompt output : List Nat) :
    (requestResult settings weights prompt output).isSome = true ↔
      (modelNextToken settings weights
        (IntegerModel.zeroFilledWindow prompt output)).isSome = true := by
  unfold requestResult
  dsimp only
  split
  · rename_i hasValue
    simp [hasValue]
  · rename_i noValue
    simp [noValue]

/-- `CanServe` holds exactly if every token is in the vocabulary, the output is not empty, and the
result is not failure. -/
theorem canServe_iff_requestResult (settings : Settings) (weights : ModelWeights settings)
    (prompt output : List Nat) :
    CanServe settings weights prompt output ↔
      (∀ token ∈ prompt ++ output, token < settings.vocabulary) ∧ output ≠ [] ∧
        (requestResult settings weights prompt output).isSome = true := by
  unfold CanServe
  rw [requestResult_isSome_iff]

end VerifiableInference

#print axioms VerifiableInference.requestResult_isSome_iff
#print axioms VerifiableInference.canServe_iff_requestResult
