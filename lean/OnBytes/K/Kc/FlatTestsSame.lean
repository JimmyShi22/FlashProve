-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/K/Kc/FlatTestsSame.lean: the five tests of OnBytes/K/Kc/FlatTests.lean agree with those of
the program `verify-on-bytes` at all arguments. Theorems with their proofs.
No premise on any argument.
Main theorems: fitsT_eq, heldT_eq, admitsT_eq, atPointT_eq, weightT_eq (the five); dotT_eq,
valuesT_eq (the two helpers).
Every test can say yes and can say no: for each of the five, at both texts, one argument at which it
says yes and one at which it says no: fits_yes, fits_no; held_yes, held_no; admits_yes, admits_no,
admits_no'; atPoint_yes, atPoint_no; weight_yes, weight_no.

Limits. These theorems name the tests of `verify-on-bytes`, as they must: so a walk by constants
that bars those tests cannot take this file's theorems for roots.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.K.Kc.FlatTests
import OnBytes.Model.Psc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.K.Kc
open OnBytes.Model (RoundForm)

theorem fitsT_eq (w : OnBytes.Psc.Weight) : fitsT w = w.fits := rfl

theorem dotT_eq (a b : List E) : dotT a b = OnBytes.Psc.dot a b := rfl

theorem heldT_eq (w : OnBytes.Psc.Weight) : heldT w = Model.weightHeld w := rfl

theorem admitsT_eq (form : RoundForm) (degree : Nat) :
    admitsT form degree = form.degreeOK degree := rfl

theorem atPointT_eq (form : RoundForm) : atPointT form = form.equality := by
  cases form <;> rfl

theorem valuesT_eq (form : RoundForm) (degree : Nat) :
    valuesT form degree = Model.roundValues form degree := by
  cases form <;> rfl

theorem weightT_eq (form : RoundForm) (z : E) (degree : Nat) :
    weightT form z degree = form.weight z degree := by
  unfold weightT RoundForm.weight
  rw [admitsT_eq, atPointT_eq, valuesT_eq]

/-! ## Each says yes somewhere and no somewhere, at both texts -/

theorem fits_yes : fitsT (OnBytes.Psc.Weight.equality zeroE 3) = true ∧
    (OnBytes.Psc.Weight.equality zeroE 3).fits = true := ⟨by decide, by decide⟩

theorem fits_no : fitsT (OnBytes.Psc.Weight.equality zeroE 1) = false ∧
    (OnBytes.Psc.Weight.equality zeroE 1).fits = false := ⟨by decide, by decide⟩

theorem held_yes : heldT (OnBytes.Psc.Weight.equality zeroE 3) = true ∧
    Model.weightHeld (OnBytes.Psc.Weight.equality zeroE 3) = true :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- At a weight that fits and does not hold: the equality weight at 0 with its fixedInv struck. -/
theorem held_no :
    heldT { OnBytes.Psc.Weight.equality zeroE 3 with fixedInv := zeroE } = false ∧
    Model.weightHeld { OnBytes.Psc.Weight.equality zeroE 3 with fixedInv := zeroE } = false :=
  ⟨by decide +kernel, by decide +kernel⟩

theorem admits_yes : admitsT .eq 1 = true ∧ RoundForm.degreeOK .eq 1 = true := ⟨rfl, rfl⟩

theorem admits_no : admitsT .eq 0 = false ∧ RoundForm.degreeOK .eq 0 = false := ⟨rfl, rfl⟩

theorem admits_no' : admitsT .nodes 65 = false ∧ RoundForm.degreeOK .nodes 65 = false := ⟨rfl, rfl⟩

theorem atPoint_yes : atPointT .eq2 = true ∧ RoundForm.equality .eq2 = true := ⟨rfl, rfl⟩

theorem atPoint_no : atPointT .sum2 = false ∧ RoundForm.equality .sum2 = false := ⟨rfl, rfl⟩

theorem weight_yes (z : E) : weightT .eq2 z 0 = some (OnBytes.Psc.Weight.equality z 3) ∧
    RoundForm.weight .eq2 z 0 = some (OnBytes.Psc.Weight.equality z 3) := ⟨rfl, rfl⟩

theorem weight_no (z : E) : weightT .eq z 0 = none ∧ RoundForm.weight .eq z 0 = none := ⟨rfl, rfl⟩

end OnBytes.K.Kc

#print axioms OnBytes.K.Kc.fitsT_eq
#print axioms OnBytes.K.Kc.heldT_eq
#print axioms OnBytes.K.Kc.admitsT_eq
#print axioms OnBytes.K.Kc.atPointT_eq
#print axioms OnBytes.K.Kc.weightT_eq
#print axioms OnBytes.K.Kc.held_yes
#print axioms OnBytes.K.Kc.held_no
