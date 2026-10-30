-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Bounds/TheCheckCanFail.lean

A test: the worst-case check `PassesWorstCaseCheck` (VerifiableInference/Bounds/NeverFails.lean) can
fail. The made-up weights `haltingWeights` (VerifiableInference/ModelGuardsAtReference.lean), at
which the model has no value on any window, do not pass it.

* `not_passesWorstCaseCheck_atHaltingWeights`. The check is not evaluated: if these weights passed,
  no range condition would ever fail at them, and
  `not_rangeConditionsNeverFail_atHaltingWeights`
  (VerifiableInference/TheModelsOwnOutputCanFail.lean) says that one does.

Limits. The test is drawn from the theorem on the check, so it would hold as well of a check that
never passes: it does not tell this check from one that is constantly false. Only weights that pass
do that, and this file shows of no weights that they pass.
-/
import VerifiableInference.Bounds.NeverFails
import VerifiableInference.TheModelsOwnOutputCanFail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference

/-- **The halting weights do not pass the worst-case check.** -/
theorem not_passesWorstCaseCheck_atHaltingWeights :
    ¬ PassesWorstCaseCheck referenceSettings haltingWeights := fun passes =>
  not_rangeConditionsNeverFail_atHaltingWeights
    (rangeConditionsNeverFail_of_passesWorstCaseCheck referenceSettings haltingWeights passes)

end VerifiableInference

#print axioms VerifiableInference.not_passesWorstCaseCheck_atHaltingWeights
