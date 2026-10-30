-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Bounds/GramTestOfStretchNumbers.lean

The length check, with its stretch numbers tested too: a predicate and two theorems.
- `PassesGramTest settings weights steps numbers`: `stretchNumbersPassGramTest`
  (IntegerModel/Bounds/GramTestOfStretchNumbers.lean) passes. It reads the sizes in the settings,
  the weights and the stretch numbers, and no prompt. It is decidable.
- `rangeConditionsNeverFail_of_passesGramTest`: at weights with stretch numbers that pass it and
  with which they pass the check (`PassesLengthWorstCaseCheck`,
  VerifiableInference/Bounds/LengthNeverFails.lean), all range conditions hold on every array of
  tokens that the model can run on.
- `modelNeverFails_of_passesGramTest`: so the model's result on a request of the right form is never
  failure.
Both theorems have two premises, and each is the value of a Boolean function. The two conclusions
are defined in VerifiableInference/ModelNeverFails.lean.
Limits: those at the head of IntegerModel/Bounds/GramTestOfStretchNumbers.lean. The tests are
sufficient, not necessary; this file says of no weights and of no numbers that they pass. The
theorems are for whoever holds the weights: nothing in a commitment, in a proof or in what a
verifier does shows that the committed weights pass. The file imports Lean's core and the model's
own files.
-/
import IntegerModel.Bounds.GramTestOfStretchNumbers
import VerifiableInference.Bounds.LengthNeverFails

set_option autoImplicit false

namespace VerifiableInference

open IntegerTransformer IntegerTransformer.Bounds

/-- The stretch numbers pass the Gram test at these weights, with this number of squarings. -/
def PassesGramTest (settings : Settings) (weights : ModelWeights settings) (steps : Nat)
    (numbers : StretchNumbers) : Prop :=
  stretchNumbersPassGramTest settings weights.val steps numbers = true

/-- The predicate can be decided: it is the value of a Boolean function. -/
instance (settings : Settings) (weights : ModelWeights settings) (steps : Nat)
    (numbers : StretchNumbers) :
    Decidable (PassesGramTest settings weights steps numbers) :=
  inferInstanceAs (Decidable (_ = true))

/-- **At weights that pass the length check with stretch numbers that pass the Gram test, no range
condition ever fails.** -/
theorem rangeConditionsNeverFail_of_passesGramTest (settings : Settings)
    (weights : ModelWeights settings) (steps : Nat) (numbers : StretchNumbers)
    (fits : PassesGramTest settings weights steps numbers)
    (passes : PassesLengthWorstCaseCheck settings weights numbers) :
    RangeConditionsNeverFail settings weights :=
  rangeConditionsNeverFail_of_passesLengthWorstCaseCheck settings weights numbers
    (hold_of_stretchNumbersPassGramTest settings weights.val steps numbers fits) passes

/-- **At weights that pass the length check with stretch numbers that pass the Gram test, the model
never fails.** -/
theorem modelNeverFails_of_passesGramTest (settings : Settings)
    (weights : ModelWeights settings) (steps : Nat) (numbers : StretchNumbers)
    (fits : PassesGramTest settings weights steps numbers)
    (passes : PassesLengthWorstCaseCheck settings weights numbers) :
    ModelNeverFails settings weights :=
  modelNeverFails_of_rangeConditionsNeverFail settings weights
    (rangeConditionsNeverFail_of_passesGramTest settings weights steps numbers fits
      passes)

end VerifiableInference

#print axioms VerifiableInference.rangeConditionsNeverFail_of_passesGramTest
#print axioms VerifiableInference.modelNeverFails_of_passesGramTest
