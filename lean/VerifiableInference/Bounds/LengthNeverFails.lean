-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Bounds/LengthNeverFails.lean

A second predicate on the weights, with stretch numbers, and three theorems.
- `PassesLengthWorstCaseCheck settings weights numbers`: `lengthWorstCaseCheck`
  (IntegerModel/Bounds/LengthCheck.lean) passes at the system's five tables. It reads the settings,
  the tables, the weights and the stretch numbers, and no prompt. It is decidable.
- `numbers.Hold settings weights.val`: each stretch number is at or above the largest singular value
  of its matrix. It is a statement on the sizes in the settings and on the weights alone, and a
  premise of the first two theorems.
- `rangeConditionsNeverFail_of_passesLengthWorstCaseCheck`: at weights that pass with stretch
  numbers that hold, all range conditions hold on every array of tokens that the model can run on.
- `modelNeverFails_of_passesLengthWorstCaseCheck`: so the model's result on a request of the right
  form is never failure.
- `modelNeverFails_of_passesFrobeniusLengthCheck`: with the Frobenius stretch numbers the premise is
  proved, and only the test is left.
Alone the predicate says nothing of the weights: the test uses the stretch numbers and does not test
them, nor that they are not negative; with numbers that are too small it can pass at weights at
which the model fails. It counts only together with `StretchNumbers.Hold`, or with one of the tests
that give it: `PassesGramTest`, `PassesScaledGramTest`, `PassesSmallerSideGramTest`
(VerifiableInference/Bounds/GramTestOfStretchNumbers.lean, ScaledGramTestOfStretchNumbers.lean,
SmallerSideGramTestOfStretchNumbers.lean).
Which theorems have tests as their only premises on the weights: here
`modelNeverFails_of_passesFrobeniusLengthCheck`; and the two theorems of each of
VerifiableInference/Bounds/GramTestOfStretchNumbers.lean, ScaledGramTestOfStretchNumbers.lean and
SmallerSideGramTestOfStretchNumbers.lean.
The two conclusions are defined in VerifiableInference/ModelNeverFails.lean.
Limits: those at the head of IntegerModel/Bounds/LengthCheck.lean. The check is sufficient, not
necessary; this file says of no weights that they pass. The theorems are for whoever holds the
weights: nothing in a commitment, in a proof or in what a verifier does shows that the committed
weights pass. The file imports Lean's core and the model's own files.
-/
import IntegerModel.Bounds.LengthNeverFails
import VerifiableInference.ModelNeverFails

set_option autoImplicit false

namespace VerifiableInference

open IntegerTransformer IntegerTransformer.Bounds

/-- The weights pass the length check with these numbers, at the system's five tables. Alone this
says nothing of the weights: the test uses the stretch numbers and does not test them, nor that they
are not negative. It counts only together with `StretchNumbers.Hold`, or with one of the tests that
give it: `PassesGramTest`, `PassesScaledGramTest`, `PassesSmallerSideGramTest`
(VerifiableInference/Bounds/GramTestOfStretchNumbers.lean, ScaledGramTestOfStretchNumbers.lean,
SmallerSideGramTestOfStretchNumbers.lean). -/
def PassesLengthWorstCaseCheck (settings : Settings) (weights : ModelWeights settings)
    (numbers : StretchNumbers) : Prop :=
  lengthWorstCaseCheck settings lookupTables weights.val numbers = true

/-- The predicate can be decided: it is the value of a Boolean function. -/
instance (settings : Settings) (weights : ModelWeights settings)
    (numbers : StretchNumbers) :
    Decidable (PassesLengthWorstCaseCheck settings weights numbers) :=
  inferInstanceAs (Decidable (_ = true))

/-- **At weights that pass the length check with stretch numbers that hold, no range condition ever
fails.** -/
theorem rangeConditionsNeverFail_of_passesLengthWorstCaseCheck (settings : Settings)
    (weights : ModelWeights settings) (numbers : StretchNumbers)
    (holds : numbers.Hold settings weights.val)
    (passes : PassesLengthWorstCaseCheck settings weights numbers) :
    RangeConditionsNeverFail settings weights := by
  intro tokens tokens_ok
  have valid := weights.property
  simp only [weightsAreValid, Bool.and_eq_true] at valid
  exact allConditionsHold_of_lengthWorstCaseCheck settings lookupTables weights.val numbers
    valid.1 holds passes tokens tokens_ok

/-- **At weights that pass the length check with stretch numbers that hold, the model never fails.**
-/
theorem modelNeverFails_of_passesLengthWorstCaseCheck (settings : Settings)
    (weights : ModelWeights settings) (numbers : StretchNumbers)
    (holds : numbers.Hold settings weights.val)
    (passes : PassesLengthWorstCaseCheck settings weights numbers) :
    ModelNeverFails settings weights :=
  modelNeverFails_of_rangeConditionsNeverFail settings weights
    (rangeConditionsNeverFail_of_passesLengthWorstCaseCheck settings weights numbers
      holds passes)

/-- The same with the Frobenius stretch numbers: the test is the only premise on the weights. -/
theorem modelNeverFails_of_passesFrobeniusLengthCheck (settings : Settings)
    (weights : ModelWeights settings)
    (passes : PassesLengthWorstCaseCheck settings weights
      (frobeniusStretchNumbers settings weights.val)) :
    ModelNeverFails settings weights :=
  modelNeverFails_of_passesLengthWorstCaseCheck settings weights _
    (frobeniusStretchNumbers_hold settings weights.val) passes

end VerifiableInference

#print axioms IntegerTransformer.Bounds.allConditionsHold_of_lengthWorstCaseCheck
#print axioms IntegerTransformer.Bounds.frobeniusStretchNumbers_hold
#print axioms VerifiableInference.rangeConditionsNeverFail_of_passesLengthWorstCaseCheck
#print axioms VerifiableInference.modelNeverFails_of_passesLengthWorstCaseCheck
#print axioms VerifiableInference.modelNeverFails_of_passesFrobeniusLengthCheck
