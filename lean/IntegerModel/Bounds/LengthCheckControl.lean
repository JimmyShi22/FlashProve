-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Bounds/LengthCheckControl.lean

A control: the check uses the stretch numbers and does not test them.

One small model, made up for this file: width 1, one dense layer, one token, which is embedded as
1,000; the value matrix has the entries 2, the output matrix the entries 2^30, and all other weights
are 0. The arguments fit together (`control_wellFormed`). Attention adds 2^40 to the stream, so
condition 1 fails at the layer's second norm, and the model has no value on the one prompt
(`control_model_eq_none`).

`lengthWorstCaseCheck` passes at these weights with the zero stretch numbers
(`control_passes_with_zeros`). These numbers do not hold (`control_zeros_do_not_hold`): the output
matrix stretches a vector. With the Frobenius stretch numbers, which hold, the check does not pass
(`control_fails_with_frobenius`). So the test alone says nothing of the weights, and the premise
`StretchNumbers.Hold` of `allConditionsHold_of_lengthWorstCaseCheck`
(IntegerModel/Bounds/LengthNeverFails.lean) cannot be left out.

The last two statements follow from that file's theorems and the failure; the others are evaluated
by Lean's kernel (`decide +kernel`), but for the two large tables: that all their keys are there,
and that their largest entry is 0, is proved. Only Lean's core library is used.
-/
import IntegerModel.Bounds.LengthNeverFails

set_option autoImplicit false

namespace IntegerTransformer.Bounds

/-! ## 1. Tables of zeros -/

/-- Every read of an array of zeros gives 0. -/
theorem entry_replicate_zero (n k : Nat) : (Array.replicate n (0 : Int)).entry k = 0 := by
  by_cases h : k < n
  · rw [entry_inside _ _ (by simpa using h)]; simp
  · rw [entry_outside _ _ (by simpa using h)]; rfl

/-- The largest absolute value in an array of zeros is 0. -/
theorem largestMagnitude_replicate_zero (n : Nat) :
    largestMagnitude (Array.replicate n (0 : Int)) = 0 := by
  unfold largestMagnitude
  have same : (fun k => magnitude ((Array.replicate n (0 : Int)).entry k)) = fun _ => 0 := by
    funext k; rw [entry_replicate_zero]; rfl
  rw [same]
  generalize (Array.replicate n (0 : Int)).size = m
  induction m with
  | zero => rfl
  | succ m ih => simp [maxUpTo, ih]

/-! ## 2. The small model -/

/-- The one layer's settings: both norms with M = 20, K = 10, eps = 1; every shift that is handed to
`roundShift` outside a norm is 1; the softmax's shift is 0; no rotary step. -/
def controlLayerSettings : LayerSettings :=
  { attentionBits := 20, attentionShift := 10, attentionEps := 1, queryShift := 1, keyShift := 1,
    valueShift := 1, rotary := false, softmaxShift := 0, outputShift := 1, feedForwardBits := 20,
    feedForwardShift := 10, feedForwardEps := 1, gateShift := 1, upShift := 1, downShift := 1,
    routerShift := 0, routedGateShift := 0, routedUpShift := 0 }

/-- One position, one dense layer, width 1, one head of two entries, one hidden unit, one token. -/
def controlSettings : Settings :=
  { positions := 1, layers := 1, width := 1, queryHeads := 1, keyValueHeads := 1, headDim := 2,
    hidden := 1, expertHidden := 0, experts := 0, vocabulary := 1, rotaryScale := 0,
    finalEps := 1, finalBits := 20, finalShift := 10, perLayer := #[controlLayerSettings] }

/-- Tables of the sizes that `wellFormed` asks for. The SiLU and the sigmoid table hold zeros. -/
def controlTables : Tables :=
  { cosine := #[#[1]], sine := #[#[0]], exponential := #[1],
    silu := { lowestKey := -32768, entries := Array.replicate 65536 0 },
    sigmoid := { lowestKey := -16384, entries := Array.replicate 32768 0 } }

/-- The one layer's weights: the value matrix has the entries 2, the output matrix 2^30. -/
def controlLayerWeights : LayerWeights :=
  { query := #[#[0, 0]], key := #[#[0, 0]], value := #[#[2, 2]], output := #[#[2 ^ 30], #[2 ^ 30]],
    shared := { gate := #[#[0]], up := #[#[0]], down := #[#[0]] }, router := #[], routed := #[] }

/-- The weights: the one token is embedded as 1,000. -/
def controlWeights : Weights :=
  { embedding := #[#[1000]], perLayer := #[controlLayerWeights], head := #[#[0]] }

/-- The stretch numbers that are all 0. -/
def zeroStretchNumbers : StretchNumbers :=
  ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0⟩

/-! ## 3. The model fails, and the check passes with zeros -/

/-- The arguments fit together. -/
theorem control_wellFormed : wellFormed controlSettings controlTables controlWeights = true := by
  have silu : controlTables.silu.covers (-32768) 32767 = true := by
    simp [KeyedTable.covers, controlTables]
  have sigmoid : controlTables.sigmoid.covers (-16384) 16383 = true := by
    simp [KeyedTable.covers, controlTables]
  unfold wellFormed
  rw [silu, sigmoid]
  decide +kernel

/-- The one token is a prompt. -/
theorem control_isPrompt : isPrompt controlSettings #[0] = true := by decide +kernel

/-- A range condition fails on that prompt. -/
theorem control_condition_fails :
    allConditionsHold controlSettings (trace controlSettings controlTables controlWeights #[0]) =
      false := by
  decide +kernel

/-- So the model has no value on it, though the arguments fit together and it is a
prompt. -/
theorem control_model_eq_none :
    model controlSettings controlTables controlWeights #[0] = none := by
  unfold model
  simp [control_condition_fails]

/-- **The check passes with the zero stretch numbers**, at weights at which the model fails. -/
theorem control_passes_with_zeros :
    lengthWorstCaseCheck controlSettings controlTables controlWeights zeroStretchNumbers =
      true := by
  have silu : largestMagnitude controlTables.silu.entries = 0 := largestMagnitude_replicate_zero _
  have sigmoid : largestMagnitude controlTables.sigmoid.entries = 0 :=
    largestMagnitude_replicate_zero _
  have routed : routedInputFits controlTables = true := by
    unfold routedInputFits
    rw [sigmoid]
    decide +kernel
  have last :
      streamLength controlSettings controlTables controlWeights zeroStretchNumbers 1 = 1003 := by
    simp only [streamLength, feedForwardAdditionLength, hiddenLength, silu]
    decide +kernel
  have layer :
      lengthLayerFits controlSettings controlTables controlWeights zeroStretchNumbers 0 = true := by
    decide +kernel
  have layers : controlSettings.layers = 1 := rfl
  unfold lengthWorstCaseCheck
  rw [routed, layers, last]
  simp only [allBelow, List.range, List.range.loop, List.all, layer]
  decide +kernel

/-! ## 4. What the theorems say of this model -/

/-- The zero stretch numbers do not hold at these weights. -/
theorem control_zeros_do_not_hold : ¬ zeroStretchNumbers.Hold controlSettings controlWeights := by
  intro holds
  have hold := allConditionsHold_of_lengthWorstCaseCheck controlSettings controlTables
    controlWeights zeroStretchNumbers control_wellFormed holds control_passes_with_zeros #[0]
    control_isPrompt
  rw [control_condition_fails] at hold
  exact absurd hold (by decide)

/-- With the Frobenius stretch numbers, which hold, the check does not pass. -/
theorem control_fails_with_frobenius :
    lengthWorstCaseCheck controlSettings controlTables controlWeights
      (frobeniusStretchNumbers controlSettings controlWeights) = false := by
  cases passes : lengthWorstCaseCheck controlSettings controlTables controlWeights
    (frobeniusStretchNumbers controlSettings controlWeights) with
  | false => rfl
  | true =>
    have hold := allConditionsHold_of_frobeniusLengthCheck controlSettings controlTables
      controlWeights control_wellFormed passes #[0] control_isPrompt
    rw [control_condition_fails] at hold
    exact absurd hold (by decide)

end IntegerTransformer.Bounds

#print axioms IntegerTransformer.Bounds.control_wellFormed
#print axioms IntegerTransformer.Bounds.control_model_eq_none
#print axioms IntegerTransformer.Bounds.control_passes_with_zeros
#print axioms IntegerTransformer.Bounds.control_zeros_do_not_hold
#print axioms IntegerTransformer.Bounds.control_fails_with_frobenius
