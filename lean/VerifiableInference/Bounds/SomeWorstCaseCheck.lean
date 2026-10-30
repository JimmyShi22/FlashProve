-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Bounds/SomeWorstCaseCheck.lean

One predicate over the worst-case checks, and what follows from it.
- `PassesSomeWorstCaseCheck settings weights`: the weights pass the first check
  (`PassesWorstCaseCheck`, VerifiableInference/Bounds/NeverFails.lean), or there are numbers that
  hold and with which they pass the least-bound check (`PassesLeastBoundWorstCaseCheck`,
  VerifiableInference/Bounds/LeastBoundNeverFails.lean). The first arm is a test. The second says
  that numbers EXIST that hold and pass: a statement, not a test.
- `passesSomeWorstCaseCheck_of_passesLeastBoundScaledGramTest`,
  `passesSomeWorstCaseCheck_of_passesFrobeniusLeastBoundCheck`: with numbers in hand that pass the
  scaled Gram test, or with the Frobenius numbers, the second arm follows from tests alone.
- `passesSomeWorstCaseCheck_of_passesLengthWorstCaseCheck`: the length check needs no arm of its
  own: what passes it with stretch numbers that hold passes the least-bound check with the matching
  numbers, which hold (IntegerModel/Bounds/LeastBoundOfLength.lean).
- `rangeConditionsNeverFail_of_passesSomeWorstCaseCheck`,
  `modelNeverFails_of_passesSomeWorstCaseCheck`, `canServe_iff_of_passesSomeWorstCaseCheck`: at such
  weights no range condition ever fails, the model's result on a request of the right form is never
  failure, and `CanServe` is its first two conditions, which do not read the weights.
Limits: those at the heads of IntegerModel/Bounds/Check.lean and
IntegerModel/Bounds/LeastBoundCheck.lean. The checks are sufficient, not necessary; this file says
of no weights that they pass. No theorem says that the first check is contained in the least-bound
check or the other way round. The theorems are for whoever holds the weights: nothing in a
commitment, in a proof or in what a verifier does shows that the committed weights pass. The file
imports Lean's core and the model's own files.
-/
import IntegerModel.Bounds.LeastBoundOfLength
import VerifiableInference.Bounds.NeverFails
import VerifiableInference.Bounds.LengthNeverFails
import VerifiableInference.Bounds.LeastBoundNeverFails

set_option autoImplicit false

namespace VerifiableInference

open IntegerTransformer IntegerTransformer.Bounds

/-- The weights pass the first worst-case check, or there are numbers that hold and with which they
pass the least-bound check. The first arm is a test; the second is a statement that such numbers
exist. -/
def PassesSomeWorstCaseCheck (settings : Settings) (weights : ModelWeights settings) : Prop :=
  PassesWorstCaseCheck settings weights
  ∨ ∃ numbers : LeastBoundNumbers,
    numbers.Hold settings lookupTables weights.val
    ∧ PassesLeastBoundWorstCaseCheck settings weights numbers

/-- Weights that pass the least-bound check with numbers that pass the scaled Gram test are among
them: both premises are tests. -/
theorem passesSomeWorstCaseCheck_of_passesLeastBoundScaledGramTest (settings : Settings)
    (weights : ModelWeights settings) (numbers : LeastBoundNumbers) (levels : LeastBoundLevels)
    (fits : PassesLeastBoundScaledGramTest settings weights numbers levels)
    (passes : PassesLeastBoundWorstCaseCheck settings weights numbers) :
    PassesSomeWorstCaseCheck settings weights :=
  Or.inr ⟨numbers,
    hold_of_leastBoundNumbersPassScaledGramTest settings lookupTables weights.val numbers levels
      fits,
    passes⟩

/-- Weights that pass the least-bound check with the Frobenius numbers are among them, for any list
of taus: the premise is a test. -/
theorem passesSomeWorstCaseCheck_of_passesFrobeniusLeastBoundCheck (settings : Settings)
    (weights : ModelWeights settings) (taus : List Int)
    (passes : PassesLeastBoundWorstCaseCheck settings weights
      (frobeniusLeastBoundNumbers settings lookupTables weights.val taus)) :
    PassesSomeWorstCaseCheck settings weights :=
  Or.inr ⟨frobeniusLeastBoundNumbers settings lookupTables weights.val taus,
    frobeniusLeastBoundNumbers_hold settings lookupTables weights.val taus, passes⟩

/-- Weights that pass the length check with stretch numbers that hold are among them. -/
theorem passesSomeWorstCaseCheck_of_passesLengthWorstCaseCheck (settings : Settings)
    (weights : ModelWeights settings) (numbers : StretchNumbers)
    (holds : numbers.Hold settings weights.val)
    (passes : PassesLengthWorstCaseCheck settings weights numbers) :
    PassesSomeWorstCaseCheck settings weights :=
  Or.inr ⟨leastBoundNumbersOf settings lookupTables weights.val [] numbers,
    leastBoundNumbersOf_hold settings lookupTables weights.val [] numbers holds,
    leastBoundWorstCaseCheck_of_lengthWorstCaseCheck settings lookupTables weights.val [] numbers
      (nonNegative_of_hold settings weights.val numbers holds) passes⟩

/-- **At weights that pass the first check, or the least-bound check with numbers that hold, no
range condition ever fails.** -/
theorem rangeConditionsNeverFail_of_passesSomeWorstCaseCheck (settings : Settings)
    (weights : ModelWeights settings) (passes : PassesSomeWorstCaseCheck settings weights) :
    RangeConditionsNeverFail settings weights := by
  rcases passes with box | ⟨numbers, holds, leastBound⟩
  · exact rangeConditionsNeverFail_of_passesWorstCaseCheck settings weights box
  · exact rangeConditionsNeverFail_of_passesLeastBoundWorstCaseCheck settings weights numbers holds
      leastBound

/-- **At weights that pass the first check, or the least-bound check with numbers that hold, the
model never fails.** -/
theorem modelNeverFails_of_passesSomeWorstCaseCheck (settings : Settings)
    (weights : ModelWeights settings) (passes : PassesSomeWorstCaseCheck settings weights) :
    ModelNeverFails settings weights :=
  modelNeverFails_of_rangeConditionsNeverFail settings weights
    (rangeConditionsNeverFail_of_passesSomeWorstCaseCheck settings weights passes)

/-- **At weights that pass the first check, or the least-bound check with numbers that hold,
`CanServe` holds exactly if every token is in the vocabulary and the output is not empty.** -/
theorem canServe_iff_of_passesSomeWorstCaseCheck (settings : Settings)
    (weights : ModelWeights settings) (passes : PassesSomeWorstCaseCheck settings weights)
    (prompt output : List Nat) :
    CanServe settings weights prompt output ↔
      (∀ token ∈ prompt ++ output, token < settings.vocabulary) ∧ output ≠ [] :=
  canServe_iff_of_rangeConditionsNeverFail settings weights
    (rangeConditionsNeverFail_of_passesSomeWorstCaseCheck settings weights passes) prompt output

end VerifiableInference

#print axioms VerifiableInference.passesSomeWorstCaseCheck_of_passesLeastBoundScaledGramTest
#print axioms VerifiableInference.passesSomeWorstCaseCheck_of_passesFrobeniusLeastBoundCheck
#print axioms VerifiableInference.passesSomeWorstCaseCheck_of_passesLengthWorstCaseCheck
#print axioms VerifiableInference.rangeConditionsNeverFail_of_passesSomeWorstCaseCheck
#print axioms VerifiableInference.modelNeverFails_of_passesSomeWorstCaseCheck
#print axioms VerifiableInference.canServe_iff_of_passesSomeWorstCaseCheck
