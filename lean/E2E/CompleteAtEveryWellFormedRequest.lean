-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/CompleteAtEveryWellFormedRequest.lean

The relation at which completeness of the interactive oracle proof is stated, `ServedRequest`
(E2E/CompleteAsIOPAtFiles.lean), at weights at which the model's own output exists. It states no
goal.

`ServedRequest b Z hr i x` says: i is the index of some weights, x is the instance that the
verifier's builder makes of a prompt and output tokens, these make a request, and the model's result
on that request is these output tokens. So the statement on completeness speaks of a prompt only if
some output is its request's result.

* `servedRequest_of_result`: at public files in scope, for every request whose result is its claimed
  output some instance is served at the index of the weights. The proof takes the instance that the
  verifier's builder makes of the request; the statement does not name it.
* `servedRequest_at_every_prompt`: so, at weights that meet `TheModelsOwnOutputExists`
  (VerifiableInference/TheModelsOwnOutput.lean), for every prompt and every length that fit a
  request there are an output of that length, which is the model's own, and an instance that is
  served.

Limits. `TheModelsOwnOutputExists` is a hypothesis on the settings and the weights. This file shows
of no weights that they meet it. Nothing is said of a request whose claimed output is not the
model's own.
-/
import VerifiableInference.TheModelsOwnOutput
import E2E.CompleteAsIOPServedLaws

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles
open VerifiableInference (ModelWeights RequestForm Token requestResult IsTheModelsOwnOutput
  TheModelsOwnOutputExists canServe_and_modelOutput_iff own_output_of_result)
open VerifierAndGoals (PublicFiles InScope readFiles settingsOfRead valid_of_read)
open FlashProve (backB build_home_of_built homeR)

variable (b : PublicFiles → ℕ) (Z : PublicFiles) {pp : Inst.Model.ScalesAndPolicy}

/-- **Where a request's result is its claimed output, some instance is served** at the index of the
weights, at public files in scope. The proof takes the instance that the verifier's builder makes of
this prompt and output; the statement does not name it: `servedRequest_at_every_prompt` does. -/
theorem servedRequest_of_result (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (weights : ModelWeights (settingsOfRead pp)) (prompt output : List Token)
    (form : RequestForm (settingsOfRead pp) prompt output)
    (result : requestResult (settingsOfRead pp) weights prompt output = some output) :
    ∃ x, ServedRequest b Z hr (backB b Z (settingsOfRead pp) weights) x := by
  obtain ⟨served, own⟩ :=
    (canServe_and_modelOutput_iff (valid_of_read hr) weights prompt output).2 ⟨form, result⟩
  obtain ⟨x, built, -⟩ := Meaning.true_of_served scope hr weights prompt output served own
  exact ⟨_, weights, prompt, output, rfl, form, result, build_home_of_built b Z built⟩

/-- **Where the model's own output exists, every prompt has a served request.** At public files in
scope, for every prompt and every length that fit a request. -/
theorem servedRequest_at_every_prompt (scope : InScope Z = true) (hr : readFiles Z = .ok pp)
    (weights : ModelWeights (settingsOfRead pp))
    (ownExists : TheModelsOwnOutputExists (settingsOfRead pp) weights)
    (prompt : List Token) (length : ℕ) (notEmpty : prompt ≠ [])
    (inVocabulary : ∀ token ∈ prompt, token < (settingsOfRead pp).vocabulary)
    (positive : 0 < length) (fits : prompt.length + length ≤ 1025) :
    ∃ (output : List Token) (x : (homeR b Z).Instance), output.length = length ∧
      IsTheModelsOwnOutput (settingsOfRead pp) weights prompt output ∧
      (homeR b Z).buildInstance (prompt, output) [] = some x ∧
      ServedRequest b Z hr (backB b Z (settingsOfRead pp) weights) x := by
  obtain ⟨output, isLength, form, result⟩ :=
    ownExists prompt length notEmpty inVocabulary positive fits
  obtain ⟨served, own⟩ :=
    (canServe_and_modelOutput_iff (valid_of_read hr) weights prompt output).2 ⟨form, result⟩
  obtain ⟨x, built, -⟩ := Meaning.true_of_served scope hr weights prompt output served own
  exact ⟨output, _, isLength, own, build_home_of_built b Z built,
    weights, prompt, output, rfl, form, result, build_home_of_built b Z built⟩

end AtPublicFiles.AtFiles

#check @AtPublicFiles.AtFiles.servedRequest_of_result
#check @AtPublicFiles.AtFiles.servedRequest_at_every_prompt
#print axioms AtPublicFiles.AtFiles.servedRequest_of_result
#print axioms AtPublicFiles.AtFiles.servedRequest_at_every_prompt
