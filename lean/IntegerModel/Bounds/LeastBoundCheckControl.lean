-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
IntegerModel/Bounds/LeastBoundCheckControl.lean

A control: the least-bound check uses its numbers and does not test them.

At the small made-up model of IntegerModel/Bounds/LengthCheckControl.lean the arguments fit together
and the model has no value on the one prompt (`control_wellFormed`, `control_model_eq_none`).
- `control_leastBound_passes_with_zeros`: `leastBoundWorstCaseCheck` passes at these weights with
  the numbers that match the zero stretch numbers (`leastBoundNumbersOf`,
  IntegerModel/Bounds/LeastBoundOfLength.lean), for every list of taus.
- `control_leastBound_zeros_do_not_hold`: these numbers do not hold.
So the test alone says nothing of the weights, and the premise `LeastBoundNumbers.Hold` of
`allConditionsHold_of_leastBoundWorstCaseCheck` (IntegerModel/Bounds/LeastBoundNeverFails.lean)
cannot be left out.
Both statements follow from theorems: the first from the length check's control and the tie of the
two checks, the second from the first, the failure and the check's theorem. Nothing is evaluated
here. The file imports Lean's core and the model's own files.
-/
import IntegerModel.Bounds.LeastBoundOfLength
import IntegerModel.Bounds.LengthCheckControl

set_option autoImplicit false

namespace IntegerTransformer.Bounds

/-- The zero stretch numbers are not negative. -/
theorem zeroStretchNumbers_nonNegative (settings : Settings) :
    zeroStretchNumbers.NonNegative settings :=
  fun _ _ =>
    ⟨Int.le_refl 0, Int.le_refl 0, Int.le_refl 0, fun _ _ _ => ⟨Int.le_refl 0, Int.le_refl 0⟩⟩

/-- **The least-bound check passes with the numbers that match the zero stretch numbers**, at
weights at which the model fails, for every list of taus. -/
theorem control_leastBound_passes_with_zeros (taus : List Int) :
    leastBoundWorstCaseCheck controlSettings controlTables controlWeights
      (leastBoundNumbersOf controlSettings controlTables controlWeights taus zeroStretchNumbers) =
      true :=
  leastBoundWorstCaseCheck_of_lengthWorstCaseCheck controlSettings controlTables controlWeights taus
    zeroStretchNumbers (zeroStretchNumbers_nonNegative controlSettings) control_passes_with_zeros

/-- These numbers do not hold at these weights. -/
theorem control_leastBound_zeros_do_not_hold (taus : List Int) :
    ¬ (leastBoundNumbersOf controlSettings controlTables controlWeights taus
      zeroStretchNumbers).Hold controlSettings controlTables controlWeights := by
  intro holds
  have hold := allConditionsHold_of_leastBoundWorstCaseCheck controlSettings controlTables
    controlWeights _ control_wellFormed holds (control_leastBound_passes_with_zeros taus) #[0]
    control_isPrompt
  rw [control_condition_fails] at hold
  exact absurd hold (by decide)

end IntegerTransformer.Bounds

#print axioms IntegerTransformer.Bounds.control_leastBound_passes_with_zeros
#print axioms IntegerTransformer.Bounds.control_leastBound_zeros_do_not_hold
