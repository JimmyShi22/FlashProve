/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
/-
Adapted from Mathlib (https://github.com/leanprover-community/mathlib4), file
Mathlib/Algebra/Polynomial/Derivative.lean, commit 5ed2965256430c3649e86755f9576b54eca72435
(v4.34.0), lines 426-441. Licence: Apache-2.0, see ThirdParty/MathlibBackport/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* Only the declarations below are taken over. This Mathlib does not have them.
* The namespace and variable lines around them are written anew, and this is an ordinary Lean file,
  not one of Lean's module system.
-/

import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Polynomial.Derivative

open Finset Polynomial
namespace Polynomial
variable {R : Type*} [Semiring R] {p : R[X]} [IsAddTorsionFree R]

@[simp] lemma derivative_eq_zero : p.derivative = 0 ↔ p.natDegree = 0 where
  mp hp := by
    obtain rfl | hp' := eq_or_ne p 0
    · exact natDegree_zero
    rw [natDegree_eq_zero_iff_degree_le_zero]
    by_contra! f_nat_degree_pos
    rw [← natDegree_pos_iff_degree_pos] at f_nat_degree_pos
    let m := p.natDegree - 1
    have hm : m + 1 = p.natDegree := tsub_add_cancel_of_le (by lia)
    have h2 := coeff_derivative p m
    rw [Polynomial.ext_iff] at hp
    rw [hp m, coeff_zero, ← Nat.cast_add_one, ← nsmul_eq_mul', eq_comm, smul_eq_zero] at h2
    replace h2 := h2.resolve_left m.succ_ne_zero
    rw [hm, ← leadingCoeff, leadingCoeff_eq_zero] at h2
    exact hp' h2
  mpr hp := by rw [eq_C_of_natDegree_eq_zero hp, derivative_C]

end Polynomial
