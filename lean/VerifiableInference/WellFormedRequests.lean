-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/WellFormedRequests.lean: the integer model's side of the heading statements.

 1. A well-formed request meets RequestForm: the formatting conditions, all four.
 2. The model's result on a request is an Option: the tokens on its window, or none.
 3. At a well-formed request: served exactly if the result is the claimed output.
 4. So completeness at well-formed requests is CompleteOn on CanServe, at valid settings.
 5. servedResult is the result that needs no hypothesis: the claimed output at a served request.
-/
import VerifiableInference.AtEveryRequestGuards
import VerifiableInference.RequestLabel

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.AtEveryRequest

open scoped ENNReal

/-- A well-formed request: `RequestForm`. The first two of its conditions are conjuncts of
`CanServe`. The other two are needed as well: at an empty prompt the result can be the claimed
output while the model has no value (`requestResult_of_emptyPrompt`), and a request that is too long
builds no instance. -/
def WellFormedRequest (settings : IntegerTransformer.Settings) (request : Request) : Prop :=
  RequestForm settings request.1 request.2

/-- The model's result on a request. -/
def modelResult (settings : IntegerTransformer.Settings) (weights : ModelWeights settings)
    (request : Request) : Option (List Token) :=
  requestResult settings weights request.1 request.2

/-- At a well-formed request the outcome is the model's result: served exactly if the result is
the claimed output. -/
theorem served_iff_result_of_wellFormed (settings : IntegerTransformer.Settings)
    (weights : ModelWeights settings) (request : Request)
    (wellFormed : WellFormedRequest settings request) :
    requestOutcome settings weights request = .served ↔
      modelResult settings weights request = some request.2 :=
  (requestOutcome_eq_served_iff settings weights request).trans
    ⟨fun served => served.2, fun isResult => ⟨wellFormed, isResult⟩⟩

/-- At valid settings a well-formed request with its claimed output as its result is one that
`CanServe` holds of, with output tokens that are the model's; and conversely. -/
theorem wellFormed_and_result_iff {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) (weights : ModelWeights settings)
    (prompt output : List Token) :
    (WellFormedRequest settings (prompt, output) ∧
        modelResult settings weights (prompt, output) = some output) ↔
      (CanServe settings weights prompt output ∧
        ∀ position (inOutput : position < output.length),
          modelNextToken settings weights (prompt ++ output.take position) =
            some output[position]) :=
  (canServe_and_modelOutput_iff valid weights prompt output).symm

/-- The result for the form without a hypothesis: the claimed output at a served request, none at
any other. -/
def servedResult (settings : IntegerTransformer.Settings) (weights : ModelWeights settings)
    (request : Request) : Option (List Token) :=
  if requestLabel settings weights request = .served then some request.2 else none

/-- At a well-formed request whose model's result is the claimed output, so is `servedResult`. -/
theorem servedResult_of_wellFormed (settings : IntegerTransformer.Settings)
    (weights : ModelWeights settings) (request : Request)
    (wellFormed : WellFormedRequest settings request)
    (isResult : modelResult settings weights request = some request.2) :
    servedResult settings weights request = some request.2 := by
  have served : requestLabel settings weights request = .served :=
    (requestLabel_eq_served_iff settings weights request).2
      ((served_iff_result_of_wellFormed settings weights request wellFormed).2 isResult)
  unfold servedResult
  exact if_pos served

end VerifiableInference.AtEveryRequest

#print axioms VerifiableInference.AtEveryRequest.served_iff_result_of_wellFormed
#print axioms VerifiableInference.AtEveryRequest.wellFormed_and_result_iff
