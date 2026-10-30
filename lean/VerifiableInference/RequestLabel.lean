-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/RequestLabel.lean: the label of a request for the integer model.

 1. The label says what became of a request: served, failed or other tokens: exactly three values.
 2. Formatting comes first: an ill-formed request gets the third word, from the request alone.
    The label is a pure function of settings, weights and request, by its type: no message, coin
    or hash query. The prover's own test reads «served», and servedAt_backThe_iff ties the two.
 3. At a well-formed request the label reads the model's result on the request's window.
 4. The window is tested first: where the model has no value on it, the label is failed.
 5. So a false claim that makes a range test fail on its own window is labelled failed.
 6. Otherwise the label is served if the result is the claimed output, and other tokens if not.
 7. The label names no token: at a false claim it says only that the tokens differ.
 8. The label is served exactly if the outcome of the request is served; bitOf gives the bit.
-/
import VerifiableInference.RequestOutcome

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.AtEveryRequest

/-- What became of a request. It holds no token and no other payload. -/
inductive Label : Type where
  /-- The model's result is the claimed output. -/
  | served : Label
  /-- The model has no value on the request's window. -/
  | failed : Label
  /-- The model's result is other tokens than the claimed ones. An ill-formed request, which
  completeness and the corollary's zero knowledge leave out, gets this word too, from the request
  alone. -/
  | otherTokens : Label
  deriving DecidableEq

/-- **The rule.** Formatting first, then the window, then the tokens. -/
def requestLabel (settings : IntegerTransformer.Settings) (weights : ModelWeights settings)
    (request : Request) : Label :=
  if RequestForm settings request.1 request.2 then
    match requestResult settings weights request.1 request.2 with
    | none => .failed
    | some tokens => if tokens = request.2 then .served else .otherTokens
  else .otherTokens

/-- An ill-formed request gets the third word, from the request alone. -/
theorem requestLabel_of_not_requestForm (settings : IntegerTransformer.Settings)
    (weights : ModelWeights settings) (request : Request)
    (illFormed : ¬ RequestForm settings request.1 request.2) :
    requestLabel settings weights request = .otherTokens := by
  unfold requestLabel
  exact if_neg illFormed

/-- At a well-formed request the label is failed exactly if the result is none. -/
theorem requestLabel_eq_failed_iff (settings : IntegerTransformer.Settings)
    (weights : ModelWeights settings) (request : Request)
    (form : RequestForm settings request.1 request.2) :
    requestLabel settings weights request = .failed ↔
      requestResult settings weights request.1 request.2 = none := by
  unfold requestLabel
  rw [if_pos form]
  split
  · next isNone => exact ⟨fun _ => isNone, fun _ => rfl⟩
  · next tokens isSome =>
    rw [isSome]
    constructor
    · intro labelled
      split at labelled <;> cases labelled
    · intro isNone
      cases isNone

/-- At a well-formed request the label is other tokens exactly if the result is tokens that are not
the claimed output. -/
theorem requestLabel_eq_otherTokens_iff (settings : IntegerTransformer.Settings)
    (weights : ModelWeights settings) (request : Request)
    (form : RequestForm settings request.1 request.2) :
    requestLabel settings weights request = .otherTokens ↔
      ∃ tokens, requestResult settings weights request.1 request.2 = some tokens ∧
        tokens ≠ request.2 := by
  unfold requestLabel
  rw [if_pos form]
  split
  · next isNone =>
    rw [isNone]
    constructor
    · intro labelled
      cases labelled
    · rintro ⟨_, isSome, _⟩
      cases isSome
  · next tokens isSome =>
    rw [isSome]
    constructor
    · intro labelled
      split at labelled
      · cases labelled
      · next differ => exact ⟨tokens, rfl, differ⟩
    · rintro ⟨other, same, differ⟩
      cases same
      exact if_neg differ

/-- The outcome of a request is one of the two. -/
theorem requestOutcome_served_or_refused (settings : IntegerTransformer.Settings)
    (weights : ModelWeights settings) (request : Request) :
    requestOutcome settings weights request = .served ∨
      requestOutcome settings weights request = .refused := by
  cases requestOutcome settings weights request
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The label is served exactly if the outcome of the request is served. -/
theorem requestLabel_eq_served_iff (settings : IntegerTransformer.Settings)
    (weights : ModelWeights settings) (request : Request) :
    requestLabel settings weights request = .served ↔
      requestOutcome settings weights request = .served := by
  rw [requestOutcome_eq_served_iff]
  unfold requestLabel
  constructor
  · intro labelled
    split at labelled
    · next form =>
      split at labelled
      · cases labelled
      · next tokens isSome =>
        split at labelled
        · next same => exact ⟨form, isSome.trans (congrArg some same)⟩
        · cases labelled
    · cases labelled
  · rintro ⟨form, isResult⟩
    rw [if_pos form, isResult]
    exact if_pos rfl

/-- The bit that a label gives: served or refused. -/
def bitOf : Label → Outcome
  | .served => .served
  | _ => .refused

/-- The bit of the label is the outcome of the request. -/
theorem bitOf_requestLabel (settings : IntegerTransformer.Settings)
    (weights : ModelWeights settings) (request : Request) :
    bitOf (requestLabel settings weights request) =
      requestOutcome settings weights request := by
  cases labelled : requestLabel settings weights request with
  | served =>
    exact ((requestLabel_eq_served_iff settings weights request).1 labelled).symm
  | failed =>
    rcases requestOutcome_served_or_refused settings weights request with served | refused
    · have := (requestLabel_eq_served_iff settings weights request).2 served
      rw [labelled] at this
      cases this
    · exact refused.symm
  | otherTokens =>
    rcases requestOutcome_served_or_refused settings weights request with served | refused
    · have := (requestLabel_eq_served_iff settings weights request).2 served
      rw [labelled] at this
      cases this
    · exact refused.symm

end VerifiableInference.AtEveryRequest

#print axioms VerifiableInference.AtEveryRequest.requestLabel_eq_served_iff
#print axioms VerifiableInference.AtEveryRequest.requestLabel_eq_failed_iff
#print axioms VerifiableInference.AtEveryRequest.requestLabel_eq_otherTokens_iff
#print axioms VerifiableInference.AtEveryRequest.bitOf_requestLabel
