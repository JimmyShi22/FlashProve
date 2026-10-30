-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Bounds/PassLengthCheckAtReferenceSettings.lean

At the settings of the library's reference table of scales (`referenceSettings`,
VerifiableInference/ModelGuardsAtReference.lean) all weights whose layers' matrices have every entry
in -800 .. 800 pass the length check with the Frobenius stretch numbers, which hold: the instance of
`passesFrobeniusLengthCheck_of_uniformLengthCheck`
(VerifiableInference/Bounds/SomeWeightsPassLengthCheck.lean) at these settings.
- `uniformLengthCheck_referenceSettings` is proved by evaluation in Lean's kernel
  (`decide +kernel`), on numbers alone.
- `passesFrobeniusLengthCheck_atReferenceSettings`: the pass.
- `passesSomeWorstCaseCheck_atReferenceSettings`: so these weights are among those of
  `PassesSomeWorstCaseCheck` (VerifiableInference/Bounds/SomeWorstCaseCheck.lean).
Limits: a bound on the entries is the only thing that is asked of the weights, and 800 is below a
fifth of the largest weight of 13 bits. Nothing is said of the converted weights of a real model.
The file imports the library's file on the reference settings, and so what that file imports.
-/
import VerifiableInference.Bounds.SomeWeightsPassLengthCheck
import VerifiableInference.Bounds.SomeWorstCaseCheck
import VerifiableInference.ModelGuardsAtReference

set_option autoImplicit false

namespace VerifiableInference

open IntegerTransformer IntegerTransformer.Bounds VerifiableInference.Bounds

/-- At the reference settings `uniformLengthCheck` passes for layers' matrices with entries in
-800 .. 800, their Frobenius norms' bounds, and any embedding that `weightsInRange` admits. -/
theorem uniformLengthCheck_referenceSettings :
    uniformLengthCheck referenceSettings 4096 4095 800 2155905152
      (uniformFrobeniusStretch referenceSettings 800) = true := by
  decide +kernel

/-- **At the reference settings all weights whose layers' matrices have every entry in -800 .. 800
pass the length check with the Frobenius stretch numbers, which hold**
(`frobeniusStretchNumbers_hold`). -/
theorem passesFrobeniusLengthCheck_atReferenceSettings (weights : ModelWeights referenceSettings)
    (small : ∀ layer, layer < referenceSettings.layers →
      LayerWithin 800 (weights.val.perLayer.entry layer)) :
    PassesLengthWorstCaseCheck referenceSettings weights
      (frobeniusStretchNumbers referenceSettings weights.val) :=
  passesFrobeniusLengthCheck_of_uniformLengthCheck referenceSettings weights 800 small
    uniformLengthCheck_referenceSettings

/-- So they are among the weights that pass the first check, or the least-bound check with numbers
that hold. -/
theorem passesSomeWorstCaseCheck_atReferenceSettings (weights : ModelWeights referenceSettings)
    (small : ∀ layer, layer < referenceSettings.layers →
      LayerWithin 800 (weights.val.perLayer.entry layer)) :
    PassesSomeWorstCaseCheck referenceSettings weights :=
  passesSomeWorstCaseCheck_of_passesLengthWorstCaseCheck referenceSettings weights _
    (frobeniusStretchNumbers_hold referenceSettings weights.val)
    (passesFrobeniusLengthCheck_atReferenceSettings weights small)

end VerifiableInference

#print axioms VerifiableInference.passesFrobeniusLengthCheck_atReferenceSettings
#print axioms VerifiableInference.passesSomeWorstCaseCheck_atReferenceSettings
