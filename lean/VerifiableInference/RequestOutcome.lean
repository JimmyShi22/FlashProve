-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/RequestOutcome.lean: the bit of a request for the integer model: served or not.
The label (VerifiableInference/RequestLabel.lean) is its finer form: served there is served here,
and failed and otherTokens there are both refused here (bitOf_requestLabel).

 1. A request is served if it is well formed and the model's result on it is its claimed output.
 2. Well formed: every token in the vocabulary, neither list empty, at most 1,025 tokens together.
 3. The model's result reads 1,024 tokens: the prompt, the claimed output, then zeros.
 4. It is the tokens that the model chooses at the output's positions, or none.
 5. None means that a token is outside the vocabulary, or that a range condition of the model fails.
 6. Every other request is refused: a result of none, of other tokens, or a request ill formed.
 7. So the model's condition stands: it decides between served and the other labels.
 8. A true output is refused if the model has no value further on in those 1,024 tokens.
 9. At valid settings the output tokens of a served request are the model's.
10. Whoever tries each candidate token learns the model's next one from this bit alone.
-/
import VerifiableInference.AtEveryRequest
import VerifiableInference.RequestResult

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.AtEveryRequest

/-- `RequestForm` is decidable. -/
instance decidableRequestForm (settings : IntegerTransformer.Settings) (prompt output : List Nat) :
    Decidable (RequestForm settings prompt output) := by
  unfold RequestForm
  exact inferInstance

/-- The outcome of a request for the integer model: served if the request is well formed and the
model's result on it is its claimed output; refused otherwise. So a result of none is a refusal: at
valid settings it means that a token of the window is outside the vocabulary, or that a range
condition of the integer model fails at one of the 1,024 positions. A result of other tokens is a
refusal too. -/
def requestOutcome (settings : IntegerTransformer.Settings) (weights : ModelWeights settings)
    (request : Request) : Outcome :=
  if RequestForm settings request.1 request.2 ∧
      requestResult settings weights request.1 request.2 = some request.2 then .served
  else .refused

/-- A request is served exactly if it is well formed and the model's result is its claimed
output. -/
theorem requestOutcome_eq_served_iff (settings : IntegerTransformer.Settings)
    (weights : ModelWeights settings) (request : Request) :
    requestOutcome settings weights request = .served ↔
      RequestForm settings request.1 request.2 ∧
        requestResult settings weights request.1 request.2 = some request.2 := by
  unfold requestOutcome
  split
  · next h => exact ⟨fun _ => h, fun _ => rfl⟩
  · next h => exact ⟨fun e => (by cases e), fun hp => absurd hp h⟩

end VerifiableInference.AtEveryRequest
