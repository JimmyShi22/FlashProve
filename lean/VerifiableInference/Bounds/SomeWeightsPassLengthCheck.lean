-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Bounds/SomeWeightsPassLengthCheck.lean

The length check (IntegerModel/Bounds/LengthCheck.lean) is not empty and does not pass everything.
- `passesLengthWorstCaseCheck_of_uniformLengthCheck`: at any settings, if `uniformLengthCheck`
  (IntegerModel/Bounds/UniformLengthCheck.lean) passes for a number `entry` and numbers `bound`,
  then all weights pass whose layers' matrices have every entry in `-entry .. entry`, with all
  stretch numbers within `bound`, whether these hold or not. Their embedding and their head matrix
  (`weights.head`: from the last stream to the logits) are free, within `weightsAreValid`.
- `passesFrobeniusLengthCheck_of_uniformLengthCheck`: the same for the Frobenius stretch numbers,
  which are within the numbers of `uniformFrobeniusStretch`.
- `passesFrobeniusLengthCheck_of_small_entries`: the instance at `exampleSettings`
  (VerifiableInference/Bounds/SomeWeightsPass.lean), with 2,048; and
  `modelNeverFails_of_small_entries`: at all these weights the model never fails.
- `mediumConstantModelWeights`: made-up weights with 2,048 at every place of every matrix, a member.
- `not_passesLengthWorstCaseCheck_largeConstantModelWeights`: the made-up weights with 4,095 at
  every place do not pass, whichever stretch numbers that hold are given. The proof evaluates
  nothing: the model fails at these weights (VerifiableInference/Bounds/SomeWeightsDoNotPass.lean),
  and weights that pass never fail. So it tests the theorem's statement, not the check's numbers.
Limits: the weights are made up. Three places of the settings have the reference table's number
(SomeWeightsPass.lean, part 2), and the settings may depend on Llama 2 7B and Llama 4 Maverick as
far as those three places do: the value shift is fixed by a test that stood while the example still
had the reference table's shifts (THIRD_PARTY.md). 2,048 is the largest power of two at which the
test passes: at 3,575 `uniformLengthCheck` refuses. All columns of the named member's head matrix
are equal, so all logits of a position are equal. `uniformLengthCheck_exampleSettings` is proved by
evaluation in Lean's kernel (`decide +kernel`). The theorems are for whoever holds the weights:
nothing in a commitment, in a proof or in what a verifier does shows that the committed weights
pass. Nothing here is about a trained model. The file imports Lean's core and the model's own files.
-/
import IntegerModel.Bounds.UniformLengthCheck
import VerifiableInference.Bounds.LengthNeverFails
import VerifiableInference.Bounds.SomeWeightsDoNotPass

set_option autoImplicit false

namespace VerifiableInference.Bounds

open IntegerTransformer IntegerTransformer.Bounds

/-- **A family of weights that pass with stretch numbers.** At any settings, take a number `entry`
and numbers `bound` for which `uniformLengthCheck` passes (with the bounds 4,096 and 4,095 of the
system's tables, and the bound of `weightsInRange` on the embedding). Then all weights whose layers'
matrices have every entry in `-entry .. entry` pass, with all stretch numbers within `bound`. The
numbers need not hold, so alone this pass says nothing of the weights; the next theorem has the
Frobenius stretch numbers, which hold. -/
theorem passesLengthWorstCaseCheck_of_uniformLengthCheck (settings : Settings)
    (weights : ModelWeights settings) (numbers : StretchNumbers) (entry : Int)
    (bound : UniformStretch)
    (small : ∀ l, l < settings.layers → LayerWithin entry (weights.val.perLayer.entry l))
    (within : StretchNumbersWithin settings numbers bound)
    (passes : uniformLengthCheck settings 4096 4095 entry 2155905152 bound = true) :
    PassesLengthWorstCaseCheck settings weights numbers := by
  have valid := weights.property
  simp only [weightsAreValid, weightsInRange, Bool.and_eq_true] at valid
  exact lengthWorstCaseCheck_of_uniformLengthCheck settings lookupTables weights.val
    numbers 4096 4095 entry 2155905152 bound cosineTable_within sineTable_within
    siluTable_within routedInputFits_lookupTables
    (matrixWithin_of_entriesWithin _ _ _ _ valid.2.1.1 (by decide) (by decide) (by decide))
    small within passes

/-- The same with the Frobenius stretch numbers. -/
theorem passesFrobeniusLengthCheck_of_uniformLengthCheck (settings : Settings)
    (weights : ModelWeights settings) (entry : Int)
    (small : ∀ l, l < settings.layers → LayerWithin entry (weights.val.perLayer.entry l))
    (passes : uniformLengthCheck settings 4096 4095 entry 2155905152
      (uniformFrobeniusStretch settings entry) = true) :
    PassesLengthWorstCaseCheck settings weights (frobeniusStretchNumbers settings weights.val) :=
  passesLengthWorstCaseCheck_of_uniformLengthCheck settings weights _ entry _ small
    (frobeniusStretchNumbers_within settings weights.val entry small) passes

/-- At the example settings `uniformLengthCheck` passes for layers' matrices with entries in
-2,048 .. 2,048, their Frobenius norms' bounds, and any embedding that `weightsInRange` admits. -/
theorem uniformLengthCheck_exampleSettings :
    uniformLengthCheck exampleSettings 4096 4095 2048 2155905152
      (uniformFrobeniusStretch exampleSettings 2048) = true := by
  decide +kernel

/-! The test passes at 3,574 and refuses at 3,575. -/
example : uniformLengthCheck exampleSettings 4096 4095 3574 2155905152
    (uniformFrobeniusStretch exampleSettings 3574) = true := by decide +kernel
example : uniformLengthCheck exampleSettings 4096 4095 3575 2155905152
    (uniformFrobeniusStretch exampleSettings 3575) = false := by decide +kernel

/-- **At the example settings all weights pass, with the Frobenius stretch numbers, whose layers'
matrices have every entry in -2,048 .. 2,048**, whatever their embedding and their head matrix are.
-/
theorem passesFrobeniusLengthCheck_of_small_entries
    (weights : ModelWeights exampleSettings)
    (small : ∀ l, l < 48 → LayerWithin 2048 (weights.val.perLayer.entry l)) :
    PassesLengthWorstCaseCheck exampleSettings weights
      (frobeniusStretchNumbers exampleSettings weights.val) :=
  passesFrobeniusLengthCheck_of_uniformLengthCheck exampleSettings weights 2048 small
    uniformLengthCheck_exampleSettings

/-- **So at all these weights the model never fails.** -/
theorem modelNeverFails_of_small_entries (weights : ModelWeights exampleSettings)
    (small : ∀ l, l < 48 → LayerWithin 2048 (weights.val.perLayer.entry l)) :
    ModelNeverFails exampleSettings weights :=
  modelNeverFails_of_passesFrobeniusLengthCheck exampleSettings weights
    (passesFrobeniusLengthCheck_of_small_entries weights small)

/-- Made-up weights at the example settings: every entry of every matrix is 2,048. -/
def mediumConstantModelWeights : ModelWeights exampleSettings :=
  ⟨constantWeights exampleSettings 2048,
    weightsAreValid_constantWeights 2048 (by decide) (by decide)⟩

/-- The layers' matrices of these weights have every entry in -2,048 .. 2,048. -/
theorem layerWithin_mediumConstantModelWeights (l : Nat) (hl : l < 48) :
    LayerWithin 2048 (mediumConstantModelWeights.val.perLayer.entry l) := by
  show LayerWithin 2048 ((constantWeights exampleSettings 2048).perLayer.entry l)
  rw [constantWeights_layer _ _ l hl]
  exact layerWithin_constantLayer _ _ _ _ (by decide)

/-- **Some weights pass with the Frobenius stretch numbers**: the made-up weights with 2,048 at
every place of every matrix. -/
theorem passesFrobeniusLengthCheck_mediumConstantModelWeights :
    PassesLengthWorstCaseCheck exampleSettings mediumConstantModelWeights
      (frobeniusStretchNumbers exampleSettings mediumConstantModelWeights.val) :=
  passesFrobeniusLengthCheck_of_small_entries _ layerWithin_mediumConstantModelWeights

/-- **Some valid weights do not pass, whichever stretch numbers that hold are given**: the made-up
weights with 4,095 at every place of every matrix, at which the model fails on every request. -/
theorem not_passesLengthWorstCaseCheck_largeConstantModelWeights
    (numbers : StretchNumbers)
    (holds : numbers.Hold exampleSettings largeConstantModelWeights.val) :
    ¬ PassesLengthWorstCaseCheck exampleSettings largeConstantModelWeights numbers :=
  fun passes => not_modelNeverFails_largeConstantModelWeights
    (modelNeverFails_of_passesLengthWorstCaseCheck _ _ numbers holds passes)

end VerifiableInference.Bounds

#print axioms VerifiableInference.Bounds.passesLengthWorstCaseCheck_of_uniformLengthCheck
#print axioms VerifiableInference.Bounds.passesFrobeniusLengthCheck_of_uniformLengthCheck
#print axioms VerifiableInference.Bounds.passesFrobeniusLengthCheck_of_small_entries
#print axioms VerifiableInference.Bounds.modelNeverFails_of_small_entries
#print axioms VerifiableInference.Bounds.passesFrobeniusLengthCheck_mediumConstantModelWeights
#print axioms VerifiableInference.Bounds.not_passesLengthWorstCaseCheck_largeConstantModelWeights
