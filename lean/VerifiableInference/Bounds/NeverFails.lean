-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Bounds/NeverFails.lean

A predicate on the weights, and three theorems: weights that pass the worst-case check never fail.
- `PassesWorstCaseCheck settings weights`: `boxWorstCaseCheck` (IntegerModel/Bounds/Check.lean)
  passes at the system's five tables. It reads the settings, the tables and the weights, and no
  prompt. It is the value of a Boolean function, so it is decidable; on evaluating it see the head
  of IntegerModel/Bounds/Check.lean.
- `rangeConditionsNeverFail_of_passesWorstCaseCheck`: at such weights all range conditions hold on
  every array of tokens that the model can run on.
- `modelNeverFails_of_passesWorstCaseCheck`: so the model's result on a request of the right form is
  never failure.
- `canServe_iff_of_passesWorstCaseCheck`: and `CanServe` is its first two conditions, which do not
  read the weights.
The first two conclusions are defined in VerifiableInference/ModelNeverFails.lean.
Limits: those at the head of IntegerModel/Bounds/Check.lean. The check is sufficient, not necessary;
this file says of no weights that they pass. The theorems are for whoever holds the weights: nothing
in a commitment, in a proof or in what a verifier does shows that the committed weights pass. The
file imports Lean's core and the model's own files.
-/
import IntegerModel.Bounds.NeverFails
import VerifiableInference.ModelNeverFails
import VerifiableInference.CanServeWhereNoConditionFails

set_option autoImplicit false

namespace VerifiableInference

open IntegerTransformer IntegerTransformer.Bounds

/-- The weights pass the worst-case check, at the system's five tables. -/
def PassesWorstCaseCheck (settings : Settings) (weights : ModelWeights settings) : Prop :=
  boxWorstCaseCheck settings lookupTables weights.val = true

instance (settings : Settings) (weights : ModelWeights settings) :
    Decidable (PassesWorstCaseCheck settings weights) :=
  inferInstanceAs (Decidable (_ = true))

/-- **At weights that pass the check no range condition ever fails.** -/
theorem rangeConditionsNeverFail_of_passesWorstCaseCheck (settings : Settings)
    (weights : ModelWeights settings) (passes : PassesWorstCaseCheck settings weights) :
    RangeConditionsNeverFail settings weights := by
  intro tokens tokens_ok
  have valid := weights.property
  simp only [weightsAreValid, Bool.and_eq_true] at valid
  exact allConditionsHold_of_boxWorstCaseCheck settings lookupTables weights.val valid.1 passes
    tokens tokens_ok

/-- **At weights that pass the check the model never fails.** -/
theorem modelNeverFails_of_passesWorstCaseCheck (settings : Settings)
    (weights : ModelWeights settings) (passes : PassesWorstCaseCheck settings weights) :
    ModelNeverFails settings weights :=
  modelNeverFails_of_rangeConditionsNeverFail settings weights
    (rangeConditionsNeverFail_of_passesWorstCaseCheck settings weights passes)

/-- **At weights that pass the check, `CanServe` holds exactly if every token is in the vocabulary
and the output is not empty.** -/
theorem canServe_iff_of_passesWorstCaseCheck (settings : Settings)
    (weights : ModelWeights settings) (passes : PassesWorstCaseCheck settings weights)
    (prompt output : List Nat) :
    CanServe settings weights prompt output ↔
      (∀ token ∈ prompt ++ output, token < settings.vocabulary) ∧ output ≠ [] :=
  canServe_iff_of_rangeConditionsNeverFail settings weights
    (rangeConditionsNeverFail_of_passesWorstCaseCheck settings weights passes) prompt output

end VerifiableInference

#print axioms IntegerTransformer.Bounds.allConditionsHold_of_boxWorstCaseCheck
#print axioms VerifiableInference.rangeConditionsNeverFail_of_passesWorstCaseCheck
#print axioms VerifiableInference.modelNeverFails_of_passesWorstCaseCheck
#print axioms VerifiableInference.canServe_iff_of_passesWorstCaseCheck
