/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro
-/
/-
Adapted from Mathlib (https://github.com/leanprover-community/mathlib4), file
Mathlib/Algebra/MvPolynomial/Degrees.lean, commit 5ed2965256430c3649e86755f9576b54eca72435
(v4.34.0), lines 277-279, 281-286, 341-345. Licence: Apache-2.0, see
ThirdParty/MathlibBackport/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* Only the declarations below are taken over. This Mathlib does not have them.
* The namespace and variable lines around them are written anew, and this is an ordinary Lean file,
  not one of Lean's module system.
-/

import Mathlib.Algebra.MvPolynomial.Degrees

namespace MvPolynomial
variable {R : Type*} {σ : Type*} [CommSemiring R] {p : MvPolynomial σ R}

@[simp] theorem degreeOf_X_self_pow [Nontrivial R] (i : σ) (k : ℕ) :
    ((X i : MvPolynomial σ R) ^ k).degreeOf i = k := by
  rw [X_pow_eq_monomial, degreeOf_monomial_eq _ _ one_ne_zero, Finsupp.single_eq_same]

lemma le_degreeOf_of_mem_support (i : σ) {s : σ →₀ ℕ} :
    s ∈ p.support → s i ≤ p.degreeOf i := fun h ↦ by
  obtain si | si := eq_or_lt_of_le <| Nat.zero_le (s i)
  · simp [← si]
  rw [degreeOf_eq_sup, Finset.le_sup_iff si]
  use s

theorem degreeOf_X_pow_of_ne {i j : σ} (k : ℕ) (h : i ≠ j) :
    ((X j : MvPolynomial σ R) ^ k).degreeOf i = 0 := by
  induction k with
  | zero => rw [pow_zero, ← C_1, degreeOf_C]
  | succ k hk => rw [pow_add, pow_one, degreeOf_mul_X_of_ne _ h, hk]

end MvPolynomial
