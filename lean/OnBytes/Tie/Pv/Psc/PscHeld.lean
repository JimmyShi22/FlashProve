-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Psc/PscHeld.lean: the condition on a weight that a round of the sub-proofs' masked
sumcheck tests before it completes a polynomial (`weightHeld`, OnBytes/Model/Psc.lean) holds for
equality weights at every z and every number of coefficients, and for the plain sum's.

Theorems with their proofs. The test compares words. At equality weights it reads neither z nor the
number of coefficients: the coefficient that is not sent is the constant, whose sum is 1, and the
public polynomial is the constant 1, so of the sums of the powers only the first is read.

Main names: `weightHeld_equality`, `weightHeld_atZero`; `fits_equality`: the sizes fit exactly if
there are at least two coefficients.

`weightHeld_plain`, `fits_plain`: the same for the plain sum's weights, where there are at least two
coefficients.


-/
import OnBytes.Model.Psc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.PscRun
open OnBytes OnBytes.Model

/-- The condition holds for equality weights, at every z and every number of coefficients. -/
theorem weightHeld_equality (z : E) (d : Nat) :
    weightHeld (OnBytes.Psc.Weight.equality z d) = true := by
  unfold weightHeld OnBytes.Psc.dot
  simp only [OnBytes.Psc.Weight.equality, List.getD_cons_zero, List.zip_cons_cons,
    List.zip_nil_right, List.foldl_cons, List.foldl_nil]
  decide +kernel

/-- The case z = 0. -/
theorem weightHeld_atZero (d : Nat) : weightHeld (OnBytes.Psc.Weight.atZero d) = true :=
  weightHeld_equality zeroE d

/-- The sizes of equality weights fit exactly if there are at least two coefficients. -/
theorem fits_equality (z : E) (d : Nat) :
    (OnBytes.Psc.Weight.equality z d).fits = true ↔ 2 ≤ d := by
  unfold OnBytes.Psc.Weight.fits
  simp only [OnBytes.Psc.Weight.equality, List.length_cons, List.length_replicate, List.length_nil,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  omega

/-- The condition holds for the plain sum's weights, where there are at least two coefficients. -/
theorem weightHeld_plain (d : Nat) (h : 2 ≤ d) :
    weightHeld (OnBytes.Psc.Weight.plain d) = true := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 2 := ⟨d - 2, by omega⟩
  unfold weightHeld OnBytes.Psc.dot
  simp only [OnBytes.Psc.Weight.plain, show n + 2 - 1 = n + 1 by omega, List.replicate_succ,
    List.getD_cons_succ, List.getD_cons_zero, List.zip_cons_cons, List.zip_nil_right,
    List.foldl_cons, List.foldl_nil]
  decide +kernel

/-- The sizes of the plain sum's weights fit exactly if there are at least two coefficients. -/
theorem fits_plain (d : Nat) : (OnBytes.Psc.Weight.plain d).fits = true ↔ 2 ≤ d := by
  unfold OnBytes.Psc.Weight.fits
  simp only [OnBytes.Psc.Weight.plain, List.length_cons, List.length_replicate, List.length_nil,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  omega

end OnBytes.PscRun

#print axioms OnBytes.PscRun.weightHeld_equality
#print axioms OnBytes.PscRun.fits_equality
#print axioms OnBytes.PscRun.weightHeld_plain
