/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Johan Commelin, Mario Carneiro, Elias Judin
-/
/-
Adapted from Mathlib (https://github.com/leanprover-community/mathlib4), file
Mathlib/Algebra/MvPolynomial/Equiv.lean, commit 5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0),
lines 64-89. Licence: Apache-2.0, see ThirdParty/MathlibBackport/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* Only the declarations below are taken over. This Mathlib does not have them.
* The namespace and variable lines around them are written anew, and this is an ordinary Lean file,
  not one of Lean's module system.
-/

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap

noncomputable section

open Polynomial Set Function Finsupp AddMonoidAlgebra
namespace MvPolynomial
variable (R : Type*) [CommSemiring R]

/-- The algebra isomorphism between multivariable polynomials indexed by a type with a unique
element and polynomials over the ground ring. -/
@[simps]
def uniqueAlgEquiv (σ : Type*) [Unique σ] : MvPolynomial σ R ≃ₐ[R] R[X] where
  toFun := eval₂ Polynomial.C fun _ => Polynomial.X
  invFun := Polynomial.eval₂ MvPolynomial.C (X default)
  left_inv := by
    let f : R[X] →+* MvPolynomial σ R := Polynomial.eval₂RingHom MvPolynomial.C (X default)
    let g : MvPolynomial σ R →+* R[X] := eval₂Hom Polynomial.C fun _ => Polynomial.X
    change ∀ p, f.comp g p = p
    apply is_id
    · ext a
      dsimp [f, g]
      rw [eval₂_C, Polynomial.eval₂_C]
    · intro i
      dsimp [f, g]
      rw [eval₂_X, Polynomial.eval₂_X]
      rw [← Unique.eq_default i]
  right_inv p :=
    Polynomial.induction_on p (fun a => by rw [Polynomial.eval₂_C, MvPolynomial.eval₂_C])
    (fun p q hp hq => by rw [Polynomial.eval₂_add, MvPolynomial.eval₂_add, hp, hq]) fun p n _ => by
      rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
        eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
  map_mul' _ _ := eval₂_mul _ _
  map_add' _ _ := eval₂_add _ _
  commutes' _ := eval₂_C _ _ _

end MvPolynomial
