-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Bounds/LeastBoundNeverFails.lean

A further predicate on the weights, with given numbers, a test of the numbers, and the theorems that
weights which pass never fail.
- `PassesLeastBoundWorstCaseCheck settings weights numbers`: `leastBoundWorstCaseCheck`
  (IntegerModel/Bounds/LeastBoundCheck.lean) passes at the system's five tables. It reads the
  settings, the tables, the weights and the numbers, and no prompt. It is decidable.
- `numbers.Hold settings lookupTables weights.val`: the numbers hold together; what that asks stands
  at `LeastBoundNumbers.Hold` (IntegerModel/Bounds/LeastBoundCheck.lean). It is a statement on the
  settings, the tables, the weights and the numbers alone, and a premise of the first two theorems.
- `rangeConditionsNeverFail_of_passesLeastBoundWorstCaseCheck`: at weights that pass with numbers
  that hold, all range conditions hold on every array of tokens that the model can run on.
- `modelNeverFails_of_passesLeastBoundWorstCaseCheck`: so the model's result on a request of the
  right form is never failure.
- `PassesLeastBoundScaledGramTest settings weights numbers levels`:
  `leastBoundNumbersPassScaledGramTest` (IntegerModel/Bounds/ScaledGramTestOfLeastBoundNumbers.lean)
  passes. It is decidable.
- `modelNeverFails_of_passesLeastBoundScaledGramTest`: with numbers that pass that test the premise
  is proved, and two tests are left.
- `modelNeverFails_of_passesFrobeniusLeastBoundCheck`: with the Frobenius numbers the premise is
  proved, and one test is left.
The two conclusions are defined in VerifiableInference/ModelNeverFails.lean.
Limits: those at the heads of IntegerModel/Bounds/LeastBoundCheck.lean and
IntegerModel/Bounds/ScaledGramTestOfLeastBoundNumbers.lean. The tests are sufficient, not necessary;
this file says of no weights and of no numbers that they pass. Alone
`PassesLeastBoundWorstCaseCheck` says nothing of the weights: the test uses the numbers and does not
test them; it counts only together with `LeastBoundNumbers.Hold`, or with
`PassesLeastBoundScaledGramTest`, which gives it. The theorems are for whoever holds the weights:
nothing in a commitment, in a proof or in what a verifier does shows that the committed weights
pass. The file imports Lean's core and the model's own files.
-/
import IntegerModel.Bounds.ScaledGramTestOfLeastBoundNumbers
import VerifiableInference.ModelNeverFails

set_option autoImplicit false

namespace VerifiableInference

open IntegerTransformer IntegerTransformer.Bounds

/-- The weights pass the least-bound check with these numbers, at the system's five tables. Alone
this says nothing of the weights: the test uses the numbers and does not test them, nor that they
are not negative. It counts only together with `LeastBoundNumbers.Hold`, or with
`PassesLeastBoundScaledGramTest`, which gives it. -/
def PassesLeastBoundWorstCaseCheck (settings : Settings) (weights : ModelWeights settings)
    (numbers : LeastBoundNumbers) : Prop :=
  leastBoundWorstCaseCheck settings lookupTables weights.val numbers = true

/-- The predicate can be decided: it is the value of a Boolean function. -/
instance (settings : Settings) (weights : ModelWeights settings)
    (numbers : LeastBoundNumbers) :
    Decidable (PassesLeastBoundWorstCaseCheck settings weights numbers) :=
  inferInstanceAs (Decidable (_ = true))

/-- **At weights that pass the least-bound check with numbers that hold, no range condition ever
fails.** -/
theorem rangeConditionsNeverFail_of_passesLeastBoundWorstCaseCheck (settings : Settings)
    (weights : ModelWeights settings) (numbers : LeastBoundNumbers)
    (holds : numbers.Hold settings lookupTables weights.val)
    (passes : PassesLeastBoundWorstCaseCheck settings weights numbers) :
    RangeConditionsNeverFail settings weights := by
  intro tokens tokens_ok
  have valid := weights.property
  simp only [weightsAreValid, Bool.and_eq_true] at valid
  exact allConditionsHold_of_leastBoundWorstCaseCheck settings lookupTables weights.val numbers
    valid.1 holds passes tokens tokens_ok

/-- **At weights that pass the least-bound check with numbers that hold, the model never fails.** -/
theorem modelNeverFails_of_passesLeastBoundWorstCaseCheck (settings : Settings)
    (weights : ModelWeights settings) (numbers : LeastBoundNumbers)
    (holds : numbers.Hold settings lookupTables weights.val)
    (passes : PassesLeastBoundWorstCaseCheck settings weights numbers) :
    ModelNeverFails settings weights :=
  modelNeverFails_of_rangeConditionsNeverFail settings weights
    (rangeConditionsNeverFail_of_passesLeastBoundWorstCaseCheck settings weights numbers holds
      passes)

/-- The least-bound check's numbers pass the scaled Gram test at these weights, with these levels.
-/
def PassesLeastBoundScaledGramTest (settings : Settings) (weights : ModelWeights settings)
    (numbers : LeastBoundNumbers) (levels : LeastBoundLevels) : Prop :=
  leastBoundNumbersPassScaledGramTest settings lookupTables weights.val numbers levels = true

/-- The predicate can be decided: it is the value of a Boolean function. -/
instance (settings : Settings) (weights : ModelWeights settings)
    (numbers : LeastBoundNumbers) (levels : LeastBoundLevels) :
    Decidable (PassesLeastBoundScaledGramTest settings weights numbers levels) :=
  inferInstanceAs (Decidable (_ = true))

/-- **At weights that pass the least-bound check with numbers that pass the scaled Gram test, the
model never fails.** Both premises are values of Boolean functions. -/
theorem modelNeverFails_of_passesLeastBoundScaledGramTest (settings : Settings)
    (weights : ModelWeights settings) (numbers : LeastBoundNumbers) (levels : LeastBoundLevels)
    (fits : PassesLeastBoundScaledGramTest settings weights numbers levels)
    (passes : PassesLeastBoundWorstCaseCheck settings weights numbers) :
    ModelNeverFails settings weights :=
  modelNeverFails_of_passesLeastBoundWorstCaseCheck settings weights numbers
    (hold_of_leastBoundNumbersPassScaledGramTest settings lookupTables weights.val numbers levels
      fits)
    passes

/-- The same with the Frobenius numbers, for any list of taus: the test is the only premise on the
weights. -/
theorem modelNeverFails_of_passesFrobeniusLeastBoundCheck (settings : Settings)
    (weights : ModelWeights settings) (taus : List Int)
    (passes : PassesLeastBoundWorstCaseCheck settings weights
      (frobeniusLeastBoundNumbers settings lookupTables weights.val taus)) :
    ModelNeverFails settings weights :=
  modelNeverFails_of_passesLeastBoundWorstCaseCheck settings weights _
    (frobeniusLeastBoundNumbers_hold settings lookupTables weights.val taus) passes

end VerifiableInference

#print axioms VerifiableInference.rangeConditionsNeverFail_of_passesLeastBoundWorstCaseCheck
#print axioms VerifiableInference.modelNeverFails_of_passesLeastBoundWorstCaseCheck
#print axioms VerifiableInference.modelNeverFails_of_passesLeastBoundScaledGramTest
#print axioms VerifiableInference.modelNeverFails_of_passesFrobeniusLeastBoundCheck
