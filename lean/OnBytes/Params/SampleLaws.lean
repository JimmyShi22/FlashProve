-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/SampleLaws.lean: what the planner's errors of out-of-domain samples enclose.

`sampleError` (OnBytes/Params/Distance.lean) prices the chance that two members of a list of code
words have the same out-of-domain sample. The rounds of the samples' seeds are priced by sums of it
(`sampleSum`, OnBytes/Params/PlanListsProx.lean, the pure form of the planner's `sampleErrors`), in
a link by twice it, and the entry for a table's record by one of it at the table's number of
answers. This file says which rational numbers these bounds enclose, with q for the number of
elements of the extension field (`Setting.cardE`): list ^ 2 / 2 times, to the power of the number of
answers, cubeBits / q, or 1 / (q - 1) for a cube of fewer than two variables.

Main definitions: `sampleShare`, `sampleShares`.
Main theorems: `encl_sampleError`, `encl_twiceSample`, `encl_sampleSum`.
What is not claimed: that the enclosed number bounds a prover's chance. Nothing on a bound that is
marked bad. At lists of one member the proved counts of these rounds are 0 (`meets_zero`,
OnBytes/Slice/HeldKindsAny.lean), and this file is not needed. Nothing on the C++ planner, of which
OnBytes/Params/ is a rendering. For proofs only; the program, that is the Lean port built from
OnBytes/, does not import this file.

-/
import OnBytes.Params.KindLaws
import OnBytes.Params.PlanListsProx

set_option autoImplicit false

namespace OnBytes.Params
open Bound

/-- The number that `sampleError` encloses. -/
def sampleShare (s : Setting) (list cubeBits answers : ℕ) : ℚ :=
  ((list * list : ℕ) : ℚ) / ((2 : ℕ) : ℚ) *
    (if 2 ≤ cubeBits then (cubeBits : ℚ) / (s.cardE : ℚ)
      else ((1 : ℕ) : ℚ) / ((s.cardE - 1 : ℕ) : ℚ)) ^ answers

/-- `sampleError` encloses `sampleShare`. -/
theorem encl_sampleError (s : Setting) (list cubeBits answers : ℕ) :
    Encl (sampleError s list cubeBits answers) (sampleShare s list cubeBits answers) := by
  unfold sampleError sampleShare
  refine encl_mul (encl_div (encl_ofNat _) (encl_ofWord 2)) (encl_pow ?_ answers)
  split
  · exact encl_fieldError s cubeBits
  · exact encl_fieldErrorNonzero s 1

/-- Twice `sampleError`, as a link's round of seeds is priced, encloses twice `sampleShare`. -/
theorem encl_twiceSample (s : Setting) (list cubeBits answers : ℕ) :
    Encl (Bound.ofWord 2 * sampleError s list cubeBits answers)
      (((2 : ℕ) : ℚ) * sampleShare s list cubeBits answers) :=
  encl_mul (encl_ofWord 2) (encl_sampleError s _ _ _)

/-- The number that `sampleSum` encloses, from y on. -/
def sampleShares (s : Setting) : List SampleSize → ℚ → ℚ
  | [], y => y
  | x :: xs, y =>
    sampleShares s xs (y + sampleShare s (largestList s x.groups) x.cubeBits s.samples)

/-- `sampleSum` from a bound that encloses y encloses `sampleShares` from y. -/
theorem encl_sampleSum (s : Setting) :
    ∀ (o : List SampleSize) {e : Bound} {y : ℚ}, Encl e y →
      Encl (sampleSum s o e) (sampleShares s o y)
  | [], _, _, h => h
  | x :: xs, _, _, h => by
      unfold sampleSum sampleShares
      exact encl_sampleSum s xs (encl_add h (encl_sampleError s _ _ _))

end OnBytes.Params

#print axioms OnBytes.Params.encl_sampleError
#print axioms OnBytes.Params.encl_twiceSample
#print axioms OnBytes.Params.encl_sampleSum
