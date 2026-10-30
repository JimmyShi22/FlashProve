-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/CanServeWhereNoConditionFails.lean

Where no range condition ever fails, `CanServe` is its two conditions on the tokens.
- `canServe_iff_of_rangeConditionsNeverFail`: under `RangeConditionsNeverFail`
  (VerifiableInference/ModelNeverFails.lean), `CanServe settings weights prompt output` holds
  exactly if every token of the prompt and of the output is of the vocabulary and the output is not
  empty. Its third condition, which depends on the weights, holds of every such prompt and output.
- `requestResult_isSome_of_rangeConditionsNeverFail`: the same for the model's result: it is not
  failure as soon as every token is of the vocabulary. The lengths are not asked.
Limits: `RangeConditionsNeverFail` is a hypothesis, and the file says of no weights that they meet
it. The definition of `CanServe` is as it was: its third condition is shown to hold at such weights.
The two conditions that are left are two of the four of `RequestForm`: `CanServe` alone also holds
of an empty prompt and of lists of any length. The file imports Lean's core and the model's own
files.
-/
import VerifiableInference.ModelNeverFails

set_option autoImplicit false

namespace VerifiableInference

open IntegerTransformer

/-- The window of a prompt and an output whose tokens are of the vocabulary is an array of tokens
that the model can run on, whatever the two lengths are. -/
theorem isPrompt_zeroFilledWindow_of_inVocabulary (settings : Settings)
    (weights : ModelWeights settings) (prompt output : List Nat)
    (inVocabulary : ∀ token ∈ prompt ++ output, token < settings.vocabulary) :
    isPrompt settings (IntegerModel.zeroFilledWindow prompt output).toArray = true := by
  have valid := weights.property
  simp only [weightsAreValid, Bool.and_eq_true] at valid
  have some_token : 0 < settings.vocabulary := (wellFormed_spec _ _ _ valid.1).1.2.2.2.2.2.1
  have positions := positions_of_modelWeights settings weights
  have length : (IntegerModel.zeroFilledWindow prompt output).length = 1024 := by
    unfold IntegerModel.zeroFilledWindow
    rw [List.length_take, List.length_append, List.length_replicate]
    omega
  have member : ∀ token, token ∈ IntegerModel.zeroFilledWindow prompt output →
      token < settings.vocabulary := by
    intro token inWindow
    rcases List.mem_append.mp (List.mem_of_mem_take inWindow) with given | filled
    · exact inVocabulary token given
    · rw [(List.mem_replicate.mp filled).2]; exact some_token
  unfold isPrompt
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.size_toArray, length]; decide
  · rw [List.size_toArray, length, positions]; decide
  · rw [Array.all_eq_true]
    intro i hi
    simp only [List.getElem_toArray, decide_eq_true_eq]
    exact member _ (List.getElem_mem _)

/-- If no range condition ever fails, the model has a value on the window of every prompt and output
whose tokens are of the vocabulary. -/
theorem modelNextToken_isSome_on_window (settings : Settings) (weights : ModelWeights settings)
    (never : RangeConditionsNeverFail settings weights) (prompt output : List Nat)
    (inVocabulary : ∀ token ∈ prompt ++ output, token < settings.vocabulary) :
    (modelNextToken settings weights
      (IntegerModel.zeroFilledWindow prompt output)).isSome = true := by
  have valid := weights.property
  simp only [weightsAreValid, Bool.and_eq_true] at valid
  have window :=
    isPrompt_zeroFilledWindow_of_inVocabulary settings weights prompt output inVocabulary
  unfold modelNextToken
  rw [(model_eq_some settings lookupTables weights.val _ _).mpr
    ⟨valid.1, window, never _ window, rfl⟩]
  rfl

/-- If no range condition ever fails, the model's result is not failure as soon as every token is of
the vocabulary. -/
theorem requestResult_isSome_of_rangeConditionsNeverFail (settings : Settings)
    (weights : ModelWeights settings) (never : RangeConditionsNeverFail settings weights)
    (prompt output : List Nat)
    (inVocabulary : ∀ token ∈ prompt ++ output, token < settings.vocabulary) :
    (requestResult settings weights prompt output).isSome = true :=
  (requestResult_isSome_iff settings weights prompt output).mpr
    (modelNextToken_isSome_on_window settings weights never prompt output inVocabulary)

/-- **If no range condition ever fails, `CanServe` asks only that every token is of the vocabulary
and that the output is not empty.** -/
theorem canServe_iff_of_rangeConditionsNeverFail (settings : Settings)
    (weights : ModelWeights settings) (never : RangeConditionsNeverFail settings weights)
    (prompt output : List Nat) :
    CanServe settings weights prompt output ↔
      (∀ token ∈ prompt ++ output, token < settings.vocabulary) ∧ output ≠ [] := by
  unfold CanServe
  constructor
  · intro served
    exact ⟨served.1, served.2.1⟩
  · intro form
    exact ⟨form.1, form.2,
      modelNextToken_isSome_on_window settings weights never prompt output form.1⟩

end VerifiableInference

#print axioms VerifiableInference.canServe_iff_of_rangeConditionsNeverFail
