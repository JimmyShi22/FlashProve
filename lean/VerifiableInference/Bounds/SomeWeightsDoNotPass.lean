-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Bounds/SomeWeightsDoNotPass.lean

The worst-case check does not pass everything, and it refuses weights at which the model fails.
`largeConstantModelWeights` are made-up valid weights at `exampleSettings`
(VerifiableInference/Bounds/SomeWeightsPass.lean): 4,095 at every place of every matrix.
- `not_passesWorstCaseCheck_largeConstantModelWeights`: they do not pass. The proof evaluates one
  test of the check in closed form: the bound on a wide value of layer 0.
- `not_allConditionsHold_largeConstantModelWeights`: on every array of tokens that the model can run
  on, a range condition fails: condition 4, in layer 0, at position 0. All rows of the embedding are
  equal, so the value there is the same on every prompt: 36,631, above 32,767.
- `requestResult_largeConstantModelWeights`: so the model's result is failure on every prompt and
  output.
Limits: the weights are made up. Three places of the settings have the reference table's number
(SomeWeightsPass.lean, part 2), and the settings may depend on Llama 2 7B and Llama 4 Maverick as
far as those three places do: the value shift is fixed by a test that stood while the example still
had the reference table's shifts (THIRD_PARTY.md). That test is this file's. The check's bound on
the wide value is nine times that value. The file imports Lean's core and the model's own files.
-/
import VerifiableInference.Bounds.SomeWeightsPass

set_option autoImplicit false

namespace VerifiableInference.Bounds

open IntegerTransformer IntegerTransformer.Bounds

/-! ## 1. The weights do not pass -/

/-- The box's bound on a column of a constant matrix, in closed form. -/
theorem boxColumnBound_constantMatrix (rows columns : Nat) (value : Int) (j : Nat)
    (inside : j < columns) :
    boxColumnBound (constantMatrix rows columns value) rows j =
      rows * (activationBound * magnitude value) := by
  unfold boxColumnBound columnBound constantMatrix
  rw [← sumOver_const]
  apply sumOver_congr
  intro k row
  rw [tabulate_read _ _ _ row, tabulate_read _ _ _ inside]

/-- What a norm returns at every place of a row of `count` equal entries `value`. -/
def normOfConstant (bits shift : Nat) (eps : Int) (count : Nat) (value : Int) : Int :=
  let root : Int := integerSquareRoot (count * (value * value) + eps).toNat
  clamp (roundShift (value * ((2 ^ bits + root / 2) / root)) shift) activationBound

/-! The two numbers that the statements below name: the check's bound on the first wide value of
layer 0, and that value itself. -/
example : roundShift (5120 * (activationBound * magnitude 4095)) 17 = 327440 := by decide +kernel
example : normOfConstant 46 32 (2 ^ 24) 5120 4095 = 229 := by decide +kernel
example : roundShift (5120 * (normOfConstant 46 32 (2 ^ 24) 5120 4095 * 4095)) 17 = 36631 := by
  decide +kernel

/-- Made-up weights at the example settings: every entry of every matrix is 4,095. -/
def largeConstantModelWeights : ModelWeights exampleSettings :=
  ⟨constantWeights exampleSettings 4095,
    weightsAreValid_constantWeights 4095 (by decide) (by decide)⟩

/-- **Some valid weights do not pass**: with 4,095 at every place, the bound on a wide value of
layer 0 is 327,440, above 32,767. -/
theorem not_passesWorstCaseCheck_largeConstantModelWeights :
    ¬ PassesWorstCaseCheck exampleSettings largeConstantModelWeights := by
  intro passes
  simp only [PassesWorstCaseCheck, boxWorstCaseCheck, Bool.and_eq_true, allBelow_spec] at passes
  have layer := passes.1.2 0 (by decide)
  simp only [layerFits, Bool.and_eq_true] at layer
  have attention := layer.1.1.2
  simp only [attentionFits, Bool.and_eq_true, allBelow_spec, decide_eq_true_eq] at attention
  have value := attention.2 0 (by decide)
  have weights : largeConstantModelWeights.val.perLayer.entry 0 =
      constantLayer exampleSettings 4095 (exampleSettings.isMixture 0) :=
    constantWeights_layer exampleSettings 4095 0 (by decide)
  rw [weights, exampleSettings_layer 0 (by decide)] at value
  simp only [constantLayer] at value
  rw [boxColumnBound_constantMatrix _ _ _ _ (by decide)] at value
  exact absurd value (by decide)

/-! ## 2. At these weights the model fails on every prompt -/

/-- A norm's result on a row of equal entries. -/
theorem rmsNorm_constant (bits shift : Nat) (eps : Int) (count : Nat) (value : Int) (k : Nat)
    (inside : k < count) :
    (rmsNorm bits shift eps (tabulate count fun _ => value)).out.entry k =
      normOfConstant bits shift eps count value := by
  have sum : (sumOver (tabulate count fun _ => value).size fun k =>
      (tabulate count fun _ => value).entry k * (tabulate count fun _ => value).entry k) =
      count * (value * value) := by
    rw [size_tabulate, ← sumOver_const]
    apply sumOver_congr
    intro k inside
    rw [tabulate_read _ _ _ inside]
  simp only [rmsNorm, normOfConstant, sum]
  rw [map_read _ _ _ (by rw [Array.size_map, size_tabulate]; exact inside),
    map_read _ _ _ (by rw [size_tabulate]; exact inside), tabulate_read _ _ _ inside]

/-- The first wide value of layer 0 at position 0, at constant weights, on every prompt. -/
theorem wideValue_constantWeights (s : Settings) (tables : Tables) (value : Int)
    (prompt : Array Nat) (prompt_ok : isPrompt s prompt = true) (some_layer : 0 < s.layers)
    (some_value : 0 < s.keyValueWidth) :
    ((((trace s tables (constantWeights s value) prompt).layer.entry 0).attention.projected.entry
      0).wideValue.entry 0) =
      roundShift (s.width * (normOfConstant (s.perLayer.entry 0).attentionBits
        (s.perLayer.entry 0).attentionShift (s.perLayer.entry 0).attentionEps s.width value *
          value)) (s.perLayer.entry 0).valueShift := by
  obtain ⟨some_token, _, tokens⟩ := isPrompt_spec s prompt prompt_ok
  have row : (prompt.map fun token => (constantWeights s value).embedding.entry token).entry 0 =
      tabulate s.width fun _ => value := by
    rw [map_read _ _ _ some_token]
    simp only [constantWeights, constantMatrix]
    rw [tabulate_read _ _ _ (tokens 0 some_token)]
  have size : 0 < (prompt.map fun token =>
      (constantWeights s value).embedding.entry token).size := by
    rw [Array.size_map]; exact some_token
  have read : (trace s tables (constantWeights s value) prompt).layer.entry 0 =
      layer s tables (constantWeights s value) 0
        (prompt.map fun token => (constantWeights s value).embedding.entry token) := by
    simp only [trace]
    rw [firstLayers_read _ _ _ _ _ _ some_layer, streamAbove_zero]
  rw [read]
  simp only [layer, attention, tabulate_read, map_read, size, projections, size_product,
    some_value, row, constantWeights_layer s value 0 some_layer, constantLayer]
  congr 1
  simp only [product, tabulate_read, some_value, (size_rmsNorm _ _ _ _).2, size_tabulate]
  rw [← sumOver_const]
  apply sumOver_congr
  intro k inside
  rw [rmsNorm_constant _ _ _ _ _ _ inside]
  simp only [constantMatrix]
  rw [tabulate_read _ _ _ inside, tabulate_read _ _ _ some_value]

/-- Every read of a vector that fits 16 bits is at most 32,767. -/
theorem read_le_of_fits16 (v : IntegerVector) (fits : fits16 v = true) (k : Nat) : v.entry k ≤ 32767 := by
  simp only [fits16, Array.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at fits
  by_cases inside : k < v.size
  · rw [entry_inside v k inside]; exact (fits k inside).2
  · rw [entry_outside v k inside]; decide

/-- **At these weights a range condition fails on every array of tokens that the model can run on**:
the first wide value of layer 0 at position 0 is 36,631. -/
theorem not_allConditionsHold_largeConstantModelWeights (tokens : Array Nat)
    (tokens_ok : isPrompt exampleSettings tokens = true) :
    allConditionsHold exampleSettings
      (trace exampleSettings lookupTables largeConstantModelWeights.val tokens) = false := by
  apply Bool.eq_false_iff.mpr
  intro hold
  have weights : largeConstantModelWeights.val = constantWeights exampleSettings 4095 := rfl
  rw [weights] at hold
  simp only [allConditionsHold, List.all_eq_true, List.mem_range, Bool.and_eq_true] at hold
  have size : (trace exampleSettings lookupTables (constantWeights exampleSettings 4095)
      tokens).embedded.size = tokens.size := by
    simp only [trace, Array.size_map]
  have first := ((hold 0 (by rw [size]; exact (isPrompt_spec _ _ tokens_ok).1)).1 0
    (by decide)).1
  simp only [attentionOk, Bool.and_eq_true] at first
  have small := read_le_of_fits16 _ first.2 0
  rw [wideValue_constantWeights exampleSettings lookupTables 4095 tokens tokens_ok (by decide)
    (by decide)] at small
  exact absurd small (by decide +kernel)

/-- So the model has no value on any list of tokens. -/
theorem modelNextToken_largeConstantModelWeights (tokens : List Nat) :
    modelNextToken exampleSettings largeConstantModelWeights tokens = none := by
  unfold modelNextToken model
  by_cases tokens_ok : isPrompt exampleSettings tokens.toArray = true
  · simp [tokens_ok, not_allConditionsHold_largeConstantModelWeights _ tokens_ok]
  · simp [tokens_ok]

/-- **So the model's result is failure on every prompt and output.** -/
theorem requestResult_largeConstantModelWeights (prompt output : List Nat) :
    requestResult exampleSettings largeConstantModelWeights prompt output = none := by
  simp [requestResult, modelNextToken_largeConstantModelWeights]

/-- The weights do not meet `ModelNeverFails`. -/
theorem not_modelNeverFails_largeConstantModelWeights :
    ¬ ModelNeverFails exampleSettings largeConstantModelWeights := by
  intro never
  refine never [0] [0] ⟨fun token inLists => ?_, by decide, by decide, by decide⟩
    (requestResult_largeConstantModelWeights [0] [0])
  have zero : token = 0 := by simpa using inLists
  rw [zero]
  decide

end VerifiableInference.Bounds

#print axioms VerifiableInference.Bounds.not_passesWorstCaseCheck_largeConstantModelWeights
#print axioms VerifiableInference.Bounds.not_allConditionsHold_largeConstantModelWeights
#print axioms VerifiableInference.Bounds.requestResult_largeConstantModelWeights
#print axioms VerifiableInference.Bounds.not_modelNeverFails_largeConstantModelWeights
