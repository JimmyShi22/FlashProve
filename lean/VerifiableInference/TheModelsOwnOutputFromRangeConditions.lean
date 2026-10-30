-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/TheModelsOwnOutputFromRangeConditions.lean

If no range condition of the integer model ever fails at given weights, the model's own output
exists at every prompt.

`RangeConditionsNeverFail settings weights` (VerifiableInference/ModelNeverFails.lean) says: on
every array of 1 to 1,024 tokens of the vocabulary all range conditions hold at all positions.
`TheModelsOwnOutputExists settings weights` (VerifiableInference/TheModelsOwnOutput.lean) says: for
every prompt and every length that fit a request there is an output of that length whose request has
that output as its result.

* `theModelsOwnOutputExists_of_rangeConditionsNeverFail`: at valid settings the first gives the
  second. The output is the greedy one of `exists_greedyOutput`
  (VerifiableInference/GreedyOutputExists.lean); that it is its request's result is
  `result_of_own_output`.

Limits. This file shows of no weights that they meet `RangeConditionsNeverFail`.
-/
import VerifiableInference.GreedyOutputExists
import VerifiableInference.TheModelsOwnOutput

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference

open IntegerTransformer

/-- **If no range condition ever fails, the model's own output exists at every prompt.** At valid
settings. -/
theorem theModelsOwnOutputExists_of_rangeConditionsNeverFail {settings : Settings}
    (valid : settingsAreValid settings = true) {weights : ModelWeights settings}
    (never : RangeConditionsNeverFail settings weights) :
    TheModelsOwnOutputExists settings weights := by
  intro prompt length notEmpty inVocabulary positive fits
  obtain ⟨output, isLength, outputInVocabulary, own⟩ :=
    exists_greedyOutput settings weights never prompt length notEmpty inVocabulary positive fits
  have outputNotEmpty : output ≠ [] := by
    intro isEmpty
    rw [isEmpty] at isLength
    exact absurd isLength.symm (Nat.ne_of_gt positive)
  have form : RequestForm settings prompt output :=
    ⟨fun token member => (List.mem_append.1 member).elim (inVocabulary token)
        (outputInVocabulary token),
      outputNotEmpty, notEmpty, by rw [isLength]; exact fits⟩
  exact ⟨output, isLength, form,
    result_of_own_output valid (modelNeverFails_of_rangeConditionsNeverFail settings weights never)
      form own⟩

end VerifiableInference

#print axioms VerifiableInference.theModelsOwnOutputExists_of_rangeConditionsNeverFail
