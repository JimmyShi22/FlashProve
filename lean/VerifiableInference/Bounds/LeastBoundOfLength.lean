-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/Bounds/LeastBoundOfLength.lean

What is shown of the length check carries over to the least-bound check, at the system's five
tables.
- `passesLeastBoundWorstCaseCheck_of_passesLengthWorstCaseCheck`: weights that pass the length
  check, with stretch numbers of which none is negative, pass the least-bound check with the
  matching numbers (`leastBoundNumbersOf`, IntegerModel/Bounds/LeastBoundOfLength.lean), for every
  list of taus.
- `passesFrobeniusLeastBoundCheck_of_passesFrobeniusLengthCheck`: the same for the two checks'
  Frobenius numbers.
- `passesFrobeniusLeastBoundCheck_of_small_entries`: at `exampleSettings` all valid weights whose
  layers' entries are in -2,048 .. 2,048 pass the least-bound check with the Frobenius numbers,
  which hold (`frobeniusLeastBoundNumbers_hold`), for every list of taus; among them
  `mediumConstantModelWeights` (`passesFrobeniusLeastBoundCheck_mediumConstantModelWeights`).
- `not_passesLeastBoundWorstCaseCheck_largeConstantModelWeights`: the made-up weights at which the
  model fails on every request do not pass the least-bound check, whichever numbers that hold are
  given. The proof evaluates nothing: the model fails at these weights
  (VerifiableInference/Bounds/SomeWeightsDoNotPass.lean), and weights that pass never fail. So it
  tests the theorem's statement, not the check's numbers.
Limits: those at the heads of IntegerModel/Bounds/LeastBoundCheck.lean and
IntegerModel/Bounds/LeastBoundOfLength.lean. The weights named here are made up; the file says
nothing of the converted weights of a real model. The theorems are for whoever holds the weights:
nothing in a commitment, in a proof or in what a verifier does shows that the committed weights
pass. The file imports Lean's core and the model's own files.
-/
import IntegerModel.Bounds.LeastBoundOfLength
import VerifiableInference.Bounds.LeastBoundNeverFails
import VerifiableInference.Bounds.SomeWeightsPassLengthCheck

set_option autoImplicit false

namespace VerifiableInference.Bounds

open IntegerTransformer IntegerTransformer.Bounds

/-- **Weights that pass the length check pass the least-bound check with the matching numbers**, for
every list of taus, if no stretch number is negative. -/
theorem passesLeastBoundWorstCaseCheck_of_passesLengthWorstCaseCheck (settings : Settings)
    (weights : ModelWeights settings) (taus : List Int) (numbers : StretchNumbers)
    (nonneg : numbers.NonNegative settings)
    (passes : PassesLengthWorstCaseCheck settings weights numbers) :
    PassesLeastBoundWorstCaseCheck settings weights
      (leastBoundNumbersOf settings lookupTables weights.val taus numbers) :=
  leastBoundWorstCaseCheck_of_lengthWorstCaseCheck settings lookupTables weights.val taus
    numbers nonneg passes

/-- The same for the two checks' Frobenius numbers: a statement on two tests alone. -/
theorem passesFrobeniusLeastBoundCheck_of_passesFrobeniusLengthCheck (settings : Settings)
    (weights : ModelWeights settings) (taus : List Int)
    (passes : PassesLengthWorstCaseCheck settings weights
      (frobeniusStretchNumbers settings weights.val)) :
    PassesLeastBoundWorstCaseCheck settings weights
      (frobeniusLeastBoundNumbers settings lookupTables weights.val taus) :=
  frobeniusLeastBoundCheck_of_frobeniusLengthCheck settings lookupTables weights.val taus passes

/-- **Some weights pass the least-bound check with numbers that hold**: at `exampleSettings`, all
valid weights whose layers' entries are in -2,048 .. 2,048, with the Frobenius numbers, which hold
(`frobeniusLeastBoundNumbers_hold`), and every list of taus. -/
theorem passesFrobeniusLeastBoundCheck_of_small_entries
    (weights : ModelWeights exampleSettings) (taus : List Int)
    (small : ∀ l, l < 48 → LayerWithin 2048 (weights.val.perLayer.entry l)) :
    PassesLeastBoundWorstCaseCheck exampleSettings weights
      (frobeniusLeastBoundNumbers exampleSettings lookupTables weights.val taus) :=
  passesFrobeniusLeastBoundCheck_of_passesFrobeniusLengthCheck _ _ taus
    (passesFrobeniusLengthCheck_of_small_entries weights small)

/-- Among them the made-up weights `mediumConstantModelWeights`, which are not zero. -/
theorem passesFrobeniusLeastBoundCheck_mediumConstantModelWeights (taus : List Int) :
    PassesLeastBoundWorstCaseCheck exampleSettings mediumConstantModelWeights
      (frobeniusLeastBoundNumbers exampleSettings lookupTables mediumConstantModelWeights.val
        taus) :=
  passesFrobeniusLeastBoundCheck_of_small_entries _ taus layerWithin_mediumConstantModelWeights

/-- **Some valid weights do not pass the least-bound check, whichever numbers that hold are given**:
the made-up weights with 4,095 at every place of every matrix, at which the model fails on every
request. -/
theorem not_passesLeastBoundWorstCaseCheck_largeConstantModelWeights
    (numbers : LeastBoundNumbers)
    (holds : numbers.Hold exampleSettings lookupTables largeConstantModelWeights.val) :
    ¬ PassesLeastBoundWorstCaseCheck exampleSettings largeConstantModelWeights numbers :=
  fun passes => not_modelNeverFails_largeConstantModelWeights
    (modelNeverFails_of_passesLeastBoundWorstCaseCheck _ _ numbers holds passes)

end VerifiableInference.Bounds

open VerifiableInference.Bounds in
#print axioms passesLeastBoundWorstCaseCheck_of_passesLengthWorstCaseCheck
open VerifiableInference.Bounds in
#print axioms passesFrobeniusLeastBoundCheck_of_passesFrobeniusLengthCheck
open VerifiableInference.Bounds in
#print axioms passesFrobeniusLeastBoundCheck_of_small_entries
open VerifiableInference.Bounds in
#print axioms passesFrobeniusLeastBoundCheck_mediumConstantModelWeights
open VerifiableInference.Bounds in
#print axioms not_passesLeastBoundWorstCaseCheck_largeConstantModelWeights
