-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ladder/RequestResultTies.lean

Completeness, and the claim under an acceptance policy, in terms of the model's result on a request
(`requestResult`, VerifiableInference/RequestResult.lean). Theorems with proofs; no definition. The
goals stand in Ladder.lean. What this file does not show: that completeness, in either form, holds
of any description.

* `completeOn_iff_completeFor`: for every argument system, `CompleteOn` on a domain is
  `CompleteFor` a claim, if the claim holds exactly where the request is in the domain and the
  output tokens are the model's.
* `completeOn_canServe_iff`: at valid settings, for the argument system of the goals: completeness
  for the requests that can be served is completeness for the requests whose result is their output
  tokens.
* `canServe_and_meetsPolicy_iff`: at all settings and every policy: together with "the output meets
  the policy", `CanServe` says no more than "the result is not failure".
* `canServe_and_meetsPolicy_exact_iff`: at valid settings and the policy of exact match the two
  together say: the prompt and the output make a request whose result is these output tokens.
-/
import Ladder
import Policy.Front.MeetsPolicyGuards
import IntegerModel.Arrays.RequestResultLaws

set_option autoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifierAndGoals

open VerifiableInference
open scoped ENNReal

/-- For every argument system: if a claim holds exactly where the weights, the prompt and the output
are in the domain and the output tokens are the model's, then completeness on the domain
(`CompleteOn`, VerifiableInference/Steps.lean) is completeness for the claim (`CompleteFor`,
Ladder.lean). -/
theorem completeOn_iff_completeFor (system : ArgumentSystem)
    (domain claim : system.Weights → List Token → List Token → Prop)
    (claimIff : ∀ weights prompt output,
      claim weights prompt output ↔
        domain weights prompt output ∧ system.IsModelOutput weights prompt output)
    (α : ℝ≥0∞) :
    CompleteOn system domain α ↔ CompleteFor system claim α := by
  constructor
  · intro complete weights prompt output holds
    exact complete weights prompt output ((claimIff _ _ _).1 holds).1 ((claimIff _ _ _).1 holds).2
  · intro complete weights prompt output inDomain isOutput
    exact complete weights prompt output ((claimIff _ _ _).2 ⟨inDomain, isOutput⟩)

/-- **Completeness for the requests that can be served is completeness for the requests whose result
is their output tokens.** At valid settings, for the argument system of the goals (`system`,
Ladder.lean, whose model is `modelNextToken settings`), with any description, public files, form
of proof, prover and parser, and for every bound α. `systemOfRecord` is one of these. -/
theorem completeOn_canServe_iff {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) (D : Description) (Z : PublicFiles) (Form : Type)
    (prove : ModelWeights settings → D.Rand → List Token → List Token → RandomizedAlgorithm Form)
    (parse : Parser D Z Form) (α : ℝ≥0∞) :
    CompleteOn (system D Z settings Form prove parse) (CanServe settings) α ↔
      CompleteFor (system D Z settings Form prove parse)
        (fun weights prompt output => RequestForm settings prompt output ∧
          requestResult settings weights prompt output = some output) α := by
  exact completeOn_iff_completeFor _ _ _
    (fun weights prompt output => (canServe_and_modelOutput_iff valid weights prompt output).symm) α

/-- At all settings, for every policy, all weights, prompts and output tokens: `CanServe` together
with "the output meets the policy" (`Policy.MeetsPolicy`, Policy/Front/MeetsPolicy.lean) holds
exactly if the result is not failure and the output meets the policy. The left side is the claim of
`G3'pol` (Ladder.lean). Under a policy that admits more than exact match the result may be other
tokens than the output: `FixedFacts.otherClaim` (Ladder.lean) has such an output. -/
theorem canServe_and_meetsPolicy_iff (settings : IntegerTransformer.Settings)
    (policy : Inst.Model.AcceptancePolicy) (weights : ModelWeights settings) (prompt output : List Token) :
    (CanServe settings weights prompt output ∧
      Policy.MeetsPolicy settings policy weights prompt output) ↔
    ((requestResult settings weights prompt output).isSome = true ∧
      Policy.MeetsPolicy settings policy weights prompt output) := by
  rw [canServe_iff_requestResult]
  constructor
  · rintro ⟨⟨-, -, notFailure⟩, meets⟩
    exact ⟨notFailure, meets⟩
  · rintro ⟨notFailure, meets⟩
    exact ⟨⟨meets.inVocabulary, meets.outputNonempty, notFailure⟩, meets⟩

/-- At valid settings and the policy of exact match (`Inst.Model.AcceptancePolicy.exact`): `CanServe` together
with "the output meets the policy" holds exactly if the prompt and the output make a request whose
result is these output tokens. -/
theorem canServe_and_meetsPolicy_exact_iff {settings : IntegerTransformer.Settings}
    (valid : settingsAreValid settings = true) (weights : ModelWeights settings)
    (prompt output : List Token) :
    (CanServe settings weights prompt output ∧
      Policy.MeetsPolicy settings Inst.Model.AcceptancePolicy.exact weights prompt output) ↔
    (RequestForm settings prompt output ∧
      requestResult settings weights prompt output = some output) := by
  rw [← canServe_and_modelOutput_iff valid, Policy.meetsPolicy_exact_iff]
  constructor
  · rintro ⟨canServe, -, isOutput⟩
    exact ⟨canServe, isOutput⟩
  · rintro ⟨canServe, isOutput⟩
    exact ⟨canServe, canServe.2.1, isOutput⟩

end VerifierAndGoals

#print axioms VerifierAndGoals.completeOn_iff_completeFor
#print axioms VerifierAndGoals.completeOn_canServe_iff
#print axioms VerifierAndGoals.canServe_and_meetsPolicy_iff
#print axioms VerifierAndGoals.canServe_and_meetsPolicy_exact_iff
