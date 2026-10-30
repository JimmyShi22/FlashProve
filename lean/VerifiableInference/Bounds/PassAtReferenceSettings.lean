-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Bounds/PassAtReferenceSettings.lean

At the settings of the library's reference table of scales (`referenceSettings`,
VerifiableInference/ModelGuardsAtReference.lean) all weights pass the worst-case check whose layers'
matrices have every entry in -200 .. 200: the instance of `passesWorstCaseCheck_of_uniformCheck`
(VerifiableInference/Bounds/SomeWeightsPass.lean) at these settings.
`uniformCheck_referenceSettings` is proved by evaluation in Lean's kernel, on numbers alone.
-/
import VerifiableInference.Bounds.SomeWeightsPass
import VerifiableInference.ModelGuardsAtReference

set_option autoImplicit false

namespace VerifiableInference

open IntegerTransformer IntegerTransformer.Bounds VerifiableInference.Bounds

/-- At the reference settings `uniformCheck` passes for entries in -200 .. 200. -/
theorem uniformCheck_referenceSettings :
    uniformCheck referenceSettings 4096 4095 200 2155905152 = true := by
  decide +kernel

/-- **At the reference settings all weights pass whose layers' matrices have every entry in
-200 .. 200.** -/
theorem passesWorstCaseCheck_atReferenceSettings (weights : ModelWeights referenceSettings)
    (small : ∀ l, l < referenceSettings.layers →
      LayerWithin 200 (weights.val.perLayer.entry l)) :
    PassesWorstCaseCheck referenceSettings weights :=
  passesWorstCaseCheck_of_uniformCheck referenceSettings weights 200 small
    uniformCheck_referenceSettings

end VerifiableInference

#print axioms VerifiableInference.passesWorstCaseCheck_atReferenceSettings
