-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Bounds/SmallerSideGramTestOfStretchNumbers.lean

The length check, with its stretch numbers tested on each matrix's smaller side: a predicate and two
theorems.
- `PassesSmallerSideGramTest settings weights levels numbers`:
  `stretchNumbersPassSmallerSideGramTest`
  (IntegerModel/Bounds/SmallerSideGramTestOfStretchNumbers.lean) passes. It reads the sizes in the
  settings, the weights, the levels and the stretch numbers, and no prompt. It is decidable.
- `rangeConditionsNeverFail_of_passesSmallerSideGramTest`: at weights with stretch numbers that pass
  it with some levels, and with which they pass the check (`PassesLengthWorstCaseCheck`,
  VerifiableInference/Bounds/LengthNeverFails.lean), all range conditions hold on every array of
  tokens that the model can run on.
- `modelNeverFails_of_passesSmallerSideGramTest`: so the model's result on a request of the right
  form is never failure.
Both theorems have two premises, and each is the value of a Boolean function. The two conclusions
are defined in VerifiableInference/ModelNeverFails.lean.
Limits: those at the head of IntegerModel/Bounds/SmallerSideGramTestOfStretchNumbers.lean. The tests
are sufficient, not necessary; this file says of no weights, no numbers and no levels that they
pass. The theorems are for whoever holds the weights: nothing in a commitment, in a proof or in what
a verifier does shows that the committed weights pass. The file imports Lean's core and the model's
own files.
-/
import IntegerModel.Bounds.SmallerSideGramTestOfStretchNumbers
import VerifiableInference.Bounds.LengthNeverFails

set_option autoImplicit false

namespace VerifiableInference

open IntegerTransformer IntegerTransformer.Bounds

/-- The stretch numbers pass the scaled Gram test on the smaller side at these weights, with these
levels. -/
def PassesSmallerSideGramTest (settings : Settings) (weights : ModelWeights settings)
    (levels : StretchLevels) (numbers : StretchNumbers) : Prop :=
  stretchNumbersPassSmallerSideGramTest settings weights.val levels numbers = true

/-- The predicate can be decided: it is the value of a Boolean function. -/
instance (settings : Settings) (weights : ModelWeights settings) (levels : StretchLevels)
    (numbers : StretchNumbers) :
    Decidable (PassesSmallerSideGramTest settings weights levels numbers) :=
  inferInstanceAs (Decidable (_ = true))

/-- **At weights that pass the length check with stretch numbers that pass the scaled Gram test on
the smaller side, no range condition ever fails.** -/
theorem rangeConditionsNeverFail_of_passesSmallerSideGramTest (settings : Settings)
    (weights : ModelWeights settings) (levels : StretchLevels) (numbers : StretchNumbers)
    (fits : PassesSmallerSideGramTest settings weights levels numbers)
    (passes : PassesLengthWorstCaseCheck settings weights numbers) :
    RangeConditionsNeverFail settings weights :=
  rangeConditionsNeverFail_of_passesLengthWorstCaseCheck settings weights numbers
    (hold_of_stretchNumbersPassSmallerSideGramTest settings weights.val levels numbers fits) passes

/-- **At weights that pass the length check with stretch numbers that pass the scaled Gram test on
the smaller side, the model never fails.** -/
theorem modelNeverFails_of_passesSmallerSideGramTest (settings : Settings)
    (weights : ModelWeights settings) (levels : StretchLevels) (numbers : StretchNumbers)
    (fits : PassesSmallerSideGramTest settings weights levels numbers)
    (passes : PassesLengthWorstCaseCheck settings weights numbers) :
    ModelNeverFails settings weights :=
  modelNeverFails_of_rangeConditionsNeverFail settings weights
    (rangeConditionsNeverFail_of_passesSmallerSideGramTest settings weights levels
      numbers fits passes)

end VerifiableInference

#print axioms VerifiableInference.rangeConditionsNeverFail_of_passesSmallerSideGramTest
#print axioms VerifiableInference.modelNeverFails_of_passesSmallerSideGramTest
