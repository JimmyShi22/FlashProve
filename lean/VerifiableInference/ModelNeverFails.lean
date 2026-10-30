-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/ModelNeverFails.lean

Two statements on given settings and weights, and the step from the first to the second.
- `RangeConditionsNeverFail`: on every array of tokens that the model can run on (`isPrompt`), all
  range conditions hold at all positions (`allConditionsHold`).
- `ModelNeverFails`: on every request of the right form (`RequestForm`) the model's result
  (`requestResult`) is not failure.
- `modelNeverFails_of_rangeConditionsNeverFail`: the first gives the second.
Both are statements on the settings and the weights alone: no prompt is given. The file says of no
weights that they meet either. It imports Lean's core and the model's own files.
-/
import IntegerModel.Readable.Reads
import VerifiableInference.RequestResult

set_option autoImplicit false

namespace VerifiableInference

open IntegerTransformer

/-- No range condition ever fails at these weights: on every array of 1 to `positions` tokens of the
vocabulary, all range conditions hold, at all positions, in all layers and at the final norm. -/
def RangeConditionsNeverFail (settings : Settings) (weights : ModelWeights settings) : Prop :=
  ∀ tokens : Array Nat, isPrompt settings tokens = true →
    allConditionsHold settings (trace settings lookupTables weights.val tokens) = true

/-- The model never fails at these weights: its result on a request of the right form is never
`none`. -/
def ModelNeverFails (settings : Settings) (weights : ModelWeights settings) : Prop :=
  ∀ prompt output : List Nat, RequestForm settings prompt output →
    requestResult settings weights prompt output ≠ none

/-- Where weights exist, the settings have 1,024 positions: the cosine table has 1,024 rows, and
`wellFormed` asks for one row for each position. -/
theorem positions_of_modelWeights (settings : Settings) (weights : ModelWeights settings) :
    settings.positions = 1024 := by
  have valid := weights.property
  simp only [weightsAreValid, Bool.and_eq_true] at valid
  have rows := (hasSize_spec _ _ _ (wellFormed_spec _ _ _ valid.1).2.2.1.1).1
  have table : lookupTables.cosine.size = 1024 := by
    simp only [lookupTables, cosineTable, size_tabulate]
  omega

/-- The window of a request of the right form is an array of tokens that the model can run on. -/
theorem isPrompt_zeroFilledWindow (settings : Settings) (weights : ModelWeights settings)
    (prompt output : List Nat) (form : RequestForm settings prompt output) :
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
    · exact form.1 token given
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

/-- **If no range condition ever fails, the model never fails.** -/
theorem modelNeverFails_of_rangeConditionsNeverFail (settings : Settings)
    (weights : ModelWeights settings) (never : RangeConditionsNeverFail settings weights) :
    ModelNeverFails settings weights := by
  intro prompt output form failed
  have valid := weights.property
  simp only [weightsAreValid, Bool.and_eq_true] at valid
  have window := isPrompt_zeroFilledWindow settings weights prompt output form
  have value : (modelNextToken settings weights
      (IntegerModel.zeroFilledWindow prompt output)).isSome = true := by
    unfold modelNextToken
    rw [(model_eq_some settings lookupTables weights.val _ _).mpr
      ⟨valid.1, window, never _ window, rfl⟩]
    rfl
  have result := (requestResult_isSome_iff settings weights prompt output).mpr value
  rw [failed] at result
  exact absurd result (by decide)

end VerifiableInference

#print axioms VerifiableInference.modelNeverFails_of_rangeConditionsNeverFail
