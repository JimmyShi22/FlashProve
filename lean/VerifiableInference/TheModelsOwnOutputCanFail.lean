-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/TheModelsOwnOutputCanFail.lean

Three tests: the hypotheses `RangeConditionsNeverFail`, `ModelNeverFails`
(VerifiableInference/ModelNeverFails.lean) and `TheModelsOwnOutputExists`
(VerifiableInference/TheModelsOwnOutput.lean) can fail. At the settings
of the reference table of scales there are valid weights, `haltingWeights`
(VerifiableInference/ModelGuardsAtReference.lean), made up for this purpose, at which the model has
no value on any window. These weights meet none of the three.

* `requestForm_zero_zero`: wherever weights exist, the prompt [0] and the output [0] make a request.
* `not_modelNeverFails_atHaltingWeights`
* `not_rangeConditionsNeverFail_atHaltingWeights`
* `not_theModelsOwnOutputExists_atHaltingWeights`

Limits. This file shows of no weights that they meet any of the three.
-/
import VerifiableInference.TheModelsOwnOutput
import VerifiableInference.ModelGuardsAtReference

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference

open IntegerTransformer

/-- Wherever weights exist, the prompt [0] and the output [0] make a request. -/
theorem requestForm_zero_zero (settings : Settings) (weights : ModelWeights settings) :
    RequestForm settings [0] [0] := by
  have valid := weights.property
  simp only [weightsAreValid, Bool.and_eq_true] at valid
  have some_token : 0 < settings.vocabulary := (wellFormed_spec _ _ _ valid.1).1.2.2.2.2.2.1
  refine ⟨fun token member => ?_, by simp, by simp, by simp⟩
  have isZero : token = 0 := by simpa using member
  rw [isZero]
  exact some_token

/-- **The halting weights do not meet `ModelNeverFails`.** -/
theorem not_modelNeverFails_atHaltingWeights :
    ¬ ModelNeverFails referenceSettings haltingWeights := fun never =>
  canServe_nowhere_atHaltingWeights [0] [0]
    (canServe_of_modelNeverFails never (requestForm_zero_zero referenceSettings haltingWeights))

/-- **The halting weights do not meet `RangeConditionsNeverFail`.** -/
theorem not_rangeConditionsNeverFail_atHaltingWeights :
    ¬ RangeConditionsNeverFail referenceSettings haltingWeights := fun never =>
  not_modelNeverFails_atHaltingWeights
    (modelNeverFails_of_rangeConditionsNeverFail referenceSettings haltingWeights never)

/-- **The halting weights do not meet `TheModelsOwnOutputExists`.** -/
theorem not_theModelsOwnOutputExists_atHaltingWeights :
    ¬ TheModelsOwnOutputExists referenceSettings haltingWeights := by
  intro ownExists
  have form := requestForm_zero_zero referenceSettings haltingWeights
  obtain ⟨output, -, formed, result⟩ := ownExists [0] 1 (by simp)
    (fun token member => form.1 token (List.mem_append_left _ member)) (by decide) (by decide)
  refine canServe_nowhere_atHaltingWeights [0] output
    ((canServe_iff_requestResult _ _ _ _).2 ⟨formed.1, formed.2.1, ?_⟩)
  rw [result]
  rfl

end VerifiableInference

#print axioms VerifiableInference.not_modelNeverFails_atHaltingWeights
#print axioms VerifiableInference.not_rangeConditionsNeverFail_atHaltingWeights
#print axioms VerifiableInference.not_theModelsOwnOutputExists_atHaltingWeights
