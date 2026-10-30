-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/TheModelsOwnOutput.lean

What follows for requests at weights at which the integer model never fails.

The integer model is partial: its result on a request (`requestResult`) is failure, `none`, if a
range condition fails somewhere on the request's window of 1,024 tokens. `ModelNeverFails`
(VerifiableInference/ModelNeverFails.lean) says of given settings and weights that this never
happens at a request of the right form. This file draws the consequences that the statements on
completeness and on zero knowledge read. It says of no weights that they meet `ModelNeverFails`.

Definitions.
* `IsTheModelsOwnOutput`: each output token is the model's next token after the prompt and the
  output tokens before it.
* `TheModelsOwnOutputExists`: for every prompt and every length that fit a request there is an
  output of that length whose request has that output as its result. It is a statement on the
  settings and the weights alone. It is used here as a hypothesis and proved nowhere in this file.
* `AtEveryRequest.HonestProofRejectedAtMost`: the probability in `ProofAcceptedWhere`, at given
  weights and one request.

Theorems.
* `canServe_of_modelNeverFails`: where the model never fails, every request of the right form meets
  `CanServe`.
* `result_of_own_output`: there, at valid settings, if the output is the model's own, the result is
  that output.
* `own_output_of_result`: at valid settings, an output that is its request's result is the model's
  own. It needs no hypothesis on the weights.
* `theModelsOwnOutput_unique`: a prompt has at most one own output of each length
  (`greedyOutput_unique`, VerifiableInference/GreedyOutputExists.lean). So "the model's own output
  of that length" names one list of tokens.
* `requestLabel_ne_failed`: where the model never fails, no request has the label `failed`.
* `proofAcceptedWhere_iff`: `ProofAcceptedWhere` in terms of `HonestProofRejectedAtMost`.

Limits. "Not failure" is not "the claimed output": a request of the right form whose claimed output
is not the model's own still has other tokens as its result, and no statement on completeness speaks
of it.
-/
import VerifiableInference.GreedyOutputExists
import VerifiableInference.WellFormedRequests
import IntegerModel.Arrays.RequestResultLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference

open IntegerTransformer

/-- The output tokens are the model's own: each is the model's next token after the prompt and the
output tokens before it. -/
def IsTheModelsOwnOutput (settings : Settings) (weights : ModelWeights settings)
    (prompt output : List Nat) : Prop :=
  ∀ position (inOutput : position < output.length),
    modelNextToken settings weights (prompt ++ output.take position) = some output[position]

/-- For every prompt and every length that fit a request, the model's own output of that length
exists: there is an output of that length such that prompt and output make a request whose result
is that output. At valid settings such an output is the model's own (`own_output_of_result`); the
definition itself speaks of the result. The prompt is not empty, its tokens are in the vocabulary,
the length is at least 1, and prompt and output together have at most 1,025 tokens. -/
def TheModelsOwnOutputExists (settings : Settings) (weights : ModelWeights settings) : Prop :=
  ∀ (prompt : List Nat) (length : Nat), prompt ≠ [] →
    (∀ token ∈ prompt, token < settings.vocabulary) → 0 < length →
    prompt.length + length ≤ 1025 →
    ∃ output : List Nat, output.length = length ∧ RequestForm settings prompt output ∧
      requestResult settings weights prompt output = some output

/-- Where the model never fails, every request of the right form meets `CanServe`. -/
theorem canServe_of_modelNeverFails {settings : Settings} {weights : ModelWeights settings}
    (never : ModelNeverFails settings weights) {prompt output : List Nat}
    (form : RequestForm settings prompt output) : CanServe settings weights prompt output :=
  (canServe_iff_requestResult settings weights prompt output).2
    ⟨form.1, form.2.1, Option.isSome_iff_ne_none.2 (never prompt output form)⟩

/-- **Where the model never fails, the model's own output is the result.** At valid settings, for a
request of the right form. -/
theorem result_of_own_output {settings : Settings} (valid : settingsAreValid settings = true)
    {weights : ModelWeights settings} (never : ModelNeverFails settings weights)
    {prompt output : List Nat} (form : RequestForm settings prompt output)
    (own : IsTheModelsOwnOutput settings weights prompt output) :
    requestResult settings weights prompt output = some output :=
  ((canServe_and_modelOutput_iff valid weights prompt output).1
    ⟨canServe_of_modelNeverFails never form, own⟩).2

/-- At valid settings, an output that is its request's result is the model's own. -/
theorem own_output_of_result {settings : Settings} (valid : settingsAreValid settings = true)
    {weights : ModelWeights settings} {prompt output : List Nat}
    (form : RequestForm settings prompt output)
    (result : requestResult settings weights prompt output = some output) :
    IsTheModelsOwnOutput settings weights prompt output :=
  ((canServe_and_modelOutput_iff valid weights prompt output).2 ⟨form, result⟩).2

/-- A prompt has at most one own output of each length. -/
theorem theModelsOwnOutput_unique {settings : Settings} {weights : ModelWeights settings}
    {prompt first second : List Nat} (sameLength : first.length = second.length)
    (firstIsOwn : IsTheModelsOwnOutput settings weights prompt first)
    (secondIsOwn : IsTheModelsOwnOutput settings weights prompt second) : first = second :=
  greedyOutput_unique settings weights prompt first second sameLength firstIsOwn secondIsOwn

/-- Where the model never fails, no request has the label `failed`. -/
theorem requestLabel_ne_failed {settings : Settings} {weights : ModelWeights settings}
    (never : ModelNeverFails settings weights) (request : AtEveryRequest.Request) :
    AtEveryRequest.requestLabel settings weights request ≠ .failed := by
  intro failed
  by_cases form : RequestForm settings request.1 request.2
  · exact never _ _ form
      ((AtEveryRequest.requestLabel_eq_failed_iff settings weights request form).1 failed)
  · rw [AtEveryRequest.requestLabel_of_not_requestForm settings weights request form] at failed
    cases failed

namespace AtEveryRequest

/-- With the honest committer and prover at these weights and this request, the proof is rejected
with probability at most `error`. The probability is over a hash function drawn at random and the
honest side's coins. It is the conclusion of `ProofAcceptedWhere`. -/
def HonestProofRejectedAtMost (system : ArgumentSystem) (weights : system.Weights)
    (request : Request) (error : ℝ≥0∞) : Prop :=
  Prob (do
      let randomness ← system.sampleCommitmentRandomness
      let commitment ← (system.commit weights randomness).toRandomized
      let proof ← system.prove weights randomness request.1 request.2
      (system.verify commitment request.1 request.2 proof).toRandomized)
    {accepted | accepted = false}
    ≤ error

/-- `ProofAcceptedWhere`, in terms of `HonestProofRejectedAtMost`. -/
theorem proofAcceptedWhere_iff (system : ArgumentSystem) (hypothesis : Request → Prop)
    (result : system.Weights → Request → Option (List Token)) (error : ℝ≥0∞) :
    ProofAcceptedWhere system hypothesis result error ↔
      ∀ (weights : system.Weights) (request : Request), hypothesis request →
        result weights request = some request.2 →
        HonestProofRejectedAtMost system weights request error :=
  Iff.rfl

end AtEveryRequest

end VerifiableInference

#print axioms VerifiableInference.canServe_of_modelNeverFails
#print axioms VerifiableInference.result_of_own_output
#print axioms VerifiableInference.own_output_of_result
#print axioms VerifiableInference.theModelsOwnOutput_unique
#print axioms VerifiableInference.requestLabel_ne_failed
#print axioms VerifiableInference.AtEveryRequest.proofAcceptedWhere_iff
