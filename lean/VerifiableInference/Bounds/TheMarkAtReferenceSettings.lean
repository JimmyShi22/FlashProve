-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Bounds/TheMarkAtReferenceSettings.lean

At the settings of the library's reference table of scales (`referenceSettings`,
VerifiableInference/ModelGuardsAtReference.lean) the mark of the made-up weights `markingWeights`
survives the shifts: the final norm's result at place 0 of the last stream's second row is positive
after the tokens 0, 1, and 0 after the tokens 1, 1. These are the two hypotheses of
`modelNextToken_markingWeightsAt_apart`
(VerifiableInference/Bounds/MarkingWeightsAtValidSettings.lean).

`markedEntry_referenceSettings` is proved by evaluation in Lean's kernel, on numbers alone.

Limits. The weights are made up; one table of scales; the statement is two facts on numbers. The
numbers on the way (the values of the first layer, their mean, the marked entry) are not shown here,
and that is meant: the statement needs only that one result is positive and the other is 0.
-/
import VerifiableInference.Bounds.MarkingWeightsAtValidSettings
import VerifiableInference.ModelGuardsAtReference

set_option autoImplicit false

namespace VerifiableInference

open IntegerTransformer IntegerTransformer.Bounds VerifiableInference.Bounds

/-- At the reference settings the mark survives. -/
theorem markedEntry_referenceSettings :
    0 < normOfOneEntry referenceSettings.finalBits referenceSettings.finalShift
      referenceSettings.finalEps (markedEntry referenceSettings 0 1) ∧
    normOfOneEntry referenceSettings.finalBits referenceSettings.finalShift
      referenceSettings.finalEps (markedEntry referenceSettings 1 1) = 0 := by
  decide +kernel

end VerifiableInference

#print axioms VerifiableInference.markedEntry_referenceSettings
