/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Yury Kudryashov
-/
/-
Adapted from Mathlib (https://github.com/leanprover-community/mathlib4), file
Mathlib/Algebra/MvPolynomial/PDeriv.lean, commit 5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0),
lines 121-134. Licence: Apache-2.0, see ThirdParty/MathlibBackport/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* Only the declarations below are taken over. This Mathlib does not have them.
* The namespace and variable lines around them are written anew, and this is an ordinary Lean file,
  not one of Lean's module system.
* Lemmas are called by their names in Lean 4.29.1 and this Mathlib: ite_eq_right became if_neg (1
  time).
-/

import Mathlib.Algebra.MvPolynomial.PDeriv

open Finsupp
namespace MvPolynomial
variable {R : Type*} {σ : Type*} [CommSemiring R]

theorem coeff_pderiv {i : σ} (p : MvPolynomial σ R) (m : σ →₀ ℕ) :
    (pderiv i p).coeff m = p.coeff (m + single i 1) * (m i + 1) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, add_mul]
  | monomial n a =>
    rw [pderiv_monomial, coeff_monomial, coeff_monomial]
    by_cases h : n = m + single i 1
    · simp [h]
    simp only [h, ↓reduceIte, zero_mul]
    by_cases hn : n i = 0
    · simp [hn]
    apply if_neg
    rwa [tsub_eq_iff_eq_add_of_le (fun _ ↦ by grind)]

end MvPolynomial
