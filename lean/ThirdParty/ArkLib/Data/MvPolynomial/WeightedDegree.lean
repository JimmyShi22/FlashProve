/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/MvPolynomial/WeightedDegree.lean, commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13.
Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 22 of the 42 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
* Lemmas are called by their names in Lean 4.29.1 and this Mathlib: ite_eq_right became if_neg (1
  time); mem_ofPred_eq became mem_setOf_eq (1 time).
-/

import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import ThirdParty.MathlibBackport.Algebra.MvPolynomial.PDeriv

/-!
# Weighted-degree bounds for multivariate polynomials

This file packages the polynomials whose monomial weights are bounded by a natural number as an
`R`-submodule and proves that the support formulation agrees with Mathlib's
`weightedTotalDegree`. In particular, the zero polynomial belongs to every bound, including bound
zero.

The bound is additive under multiplication.  Consequently, the weight-zero piece is also closed
under multiplication, while a positive fixed bound is not in general.

The finiteness and finrank results below require every variable weight to be nonzero.  This
hypothesis is load-bearing: if a variable has weight zero, all of its powers remain in every
bounded piece.  In particular, a downstream interpolation weight with untracked, weight-zero
variables must add separate degree caps before using a finite-dimensional count.

## Main declarations

* `restrictWeightedDegree`: the bounded-support submodule.
* `weightedTotalDegree_bind₁_le` and `weightedTotalDegree_aeval_le`: substitution bounds with
  induced source weights.
* `bind₁_mem_restrictWeightedDegree`: preservation under prescribed-weight substitution.
* `weightedTotalDegree_pderiv_le_sub`: a partial derivative in `X i` lowers the weighted total
  degree by at least `w i`, in every characteristic.
* `degreeOf_le_weightedTotalDegree`: if `X i` has positive weight, its degree is bounded by the
  weighted total degree.
* `natDegree_aeval_le_weightedTotalDegree` and `natDegree_aeval_le_weightedTotalDegree_of_le`:
  substituting univariate polynomials gives a univariate polynomial whose `natDegree` is at most
  the weighted total degree, with the weight of `i` being (a bound on) `natDegree (f i)`.
* `basisRestrictWeightedDegree` and `restrictWeightedDegreeCoeff`: its monomial basis and
  coefficient projections.
* `finrank_restrictWeightedDegree`: the finite positive-weight dimension formula.

## References

The partial-derivative and univariate-substitution bounds are extracted from
`HiddenDerivative/RootFinding/DegreeBounds/SpecializationDegree.lean`, under
`ArkLib/Data/CodingTheory/ReedSolomon/`, at ArkLib revision
a5aa2677fee4e3a79d6bb05136631cce4a08587d. The source theorems
`ReedSolomon.HiddenDerivative.weightedTotalDegree_pderiv_le_sub` and
`ReedSolomon.HiddenDerivative.weightedTotalDegree_pderiv_le` were stated for differential
polynomials, whose variables are jet variables; here they hold for an arbitrary variable type.
The source theorem `ReedSolomon.HiddenDerivative.natDegree_differentialSpecialization_le` is the
special case of `natDegree_aeval_le_weightedTotalDegree_of_le` in which the substituted
polynomials are `X` and the Hasse derivatives of one bounded polynomial. That jet-specific
statement, the separant corollaries, and the root-counting wrapper stay with their consumers and
are not ported here.
-/

noncomputable section

open scoped BigOperators

open Finsupp Module

namespace MvPolynomial

variable {σ R : Type*} [CommSemiring R]

/-- The `R`-submodule of multivariate polynomials all of whose monomials have `w`-weight at most
`d`. -/
def restrictWeightedDegree (w : σ → ℕ) (d : ℕ) : Submodule R (MvPolynomial σ R) :=
  restrictSupport R {m | m.weight w ≤ d}

/-- Membership in `restrictWeightedDegree` is exactly the pointwise weight bound on support. -/
theorem mem_restrictWeightedDegree {w : σ → ℕ} {d : ℕ} {p : MvPolynomial σ R} :
    p ∈ restrictWeightedDegree (R := R) w d ↔ ∀ m ∈ p.support, m.weight w ≤ d := by
  rfl

/-- The support formulation agrees with mathlib's `weightedTotalDegree`.  In particular, it gives
the zero polynomial weighted total degree zero, hence membership at bound zero. -/
theorem mem_restrictWeightedDegree_iff_weightedTotalDegree_le {w : σ → ℕ} {d : ℕ}
    {p : MvPolynomial σ R} :
    p ∈ restrictWeightedDegree (R := R) w d ↔ p.weightedTotalDegree w ≤ d := by
  rw [mem_restrictWeightedDegree, weightedTotalDegree, Finset.sup_le_iff]

/-- Assigning weight one to every variable recovers mathlib's total-degree submodule. -/
@[simp]
theorem restrictWeightedDegree_one (d : ℕ) :
    restrictWeightedDegree (R := R) (fun _ : σ => 1) d = restrictTotalDegree σ R d := by
  ext p
  rw [mem_restrictWeightedDegree_iff_weightedTotalDegree_le, mem_restrictTotalDegree]
  change weightedTotalDegree (1 : σ → ℕ) p ≤ d ↔ p.totalDegree ≤ d
  rw [weightedTotalDegree_one]

/-- A monomial is bounded exactly when its exponent has bounded weight, unless its coefficient
vanishes. -/
@[simp]
theorem monomial_mem_restrictWeightedDegree (w : σ → ℕ) (d : ℕ) (m : σ →₀ ℕ) (r : R) :
    monomial m r ∈ restrictWeightedDegree (R := R) w d ↔ m.weight w ≤ d ∨ r = 0 := by
  simpa only [restrictWeightedDegree, Set.mem_setOf_eq] using
    (monomial_mem_restrictSupport (R := R) (s := {m | m.weight w ≤ d}) (m := m) (r := r))

/-- Constant polynomials have weighted degree at most every natural-number bound. -/
@[simp]
theorem C_mem_restrictWeightedDegree (w : σ → ℕ) (d : ℕ) (r : R) :
    C r ∈ restrictWeightedDegree (R := R) w d := by
  change monomial (0 : σ →₀ ℕ) r ∈ restrictWeightedDegree (R := R) w d
  exact (monomial_mem_restrictWeightedDegree w d 0 r).mpr (Or.inl (by simp))

/-- The variable `X i` lies in every bound at least its assigned weight. -/
theorem X_mem_restrictWeightedDegree (w : σ → ℕ) (d : ℕ) (i : σ) (hi : w i ≤ d) :
    X i ∈ restrictWeightedDegree (R := R) w d := by
  rw [X, monomial_mem_restrictWeightedDegree]
  simp [weight_single, hi]

/-! ### Weighted-degree bounds under substitution -/

/-- Weighted total degree is subadditive under multiplication. -/
theorem weightedTotalDegree_mul_le (w : σ → ℕ) (p q : MvPolynomial σ R) :
    weightedTotalDegree w (p * q) ≤ weightedTotalDegree w p + weightedTotalDegree w q :=
  AddMonoidAlgebra.supDegree_mul_le (map_add (weight w))

/-- A constant has weighted total degree zero, including the zero constant. -/
@[simp]
theorem weightedTotalDegree_C (w : σ → ℕ) (r : R) :
    weightedTotalDegree w (C r : MvPolynomial σ R) = 0 := by
  classical
  rw [weightedTotalDegree, support_C]
  split_ifs <;> simp

/-- The weighted total degree of a nonzero monomial is the weight of its exponent. -/
theorem weightedTotalDegree_monomial (w : σ → ℕ) (m : σ →₀ ℕ) (r : R) (hr : r ≠ 0) :
    weightedTotalDegree w (monomial m r) = weight w m := by
  classical
  rw [weightedTotalDegree, support_monomial, if_neg hr]
  simp

/-- Taking the `n`th power multiplies the weighted-total-degree upper bound by `n`. -/
theorem weightedTotalDegree_pow_le (w : σ → ℕ) (p : MvPolynomial σ R) (n : ℕ) :
    weightedTotalDegree w (p ^ n) ≤ n * weightedTotalDegree w p := by
  induction n with
  | zero =>
      rw [pow_zero, ← C_1, weightedTotalDegree_C, zero_mul]
  | succ n ih =>
      rw [pow_succ]
      calc
        weightedTotalDegree w (p ^ n * p) ≤
            weightedTotalDegree w (p ^ n) + weightedTotalDegree w p :=
          weightedTotalDegree_mul_le _ _ _
        _ ≤ n * weightedTotalDegree w p + weightedTotalDegree w p :=
          Nat.add_le_add_right ih _
        _ = (n + 1) * weightedTotalDegree w p := by rw [add_mul, one_mul]

private theorem weightedTotalDegree_bind₁_monomial_le {τ : Type*} (v : τ → ℕ)
    (f : σ → MvPolynomial τ R) (m : σ →₀ ℕ) (r : R) :
    weightedTotalDegree v (bind₁ f (monomial m r)) ≤
      weight (fun i => weightedTotalDegree v (f i)) m := by
  rw [bind₁_monomial]
  calc
    weightedTotalDegree v (C r * ∏ i ∈ m.support, f i ^ m i) ≤
        weightedTotalDegree v (C r) +
          weightedTotalDegree v (∏ i ∈ m.support, f i ^ m i) :=
      weightedTotalDegree_mul_le _ _ _
    _ ≤ 0 + ∑ i ∈ m.support, weightedTotalDegree v (f i ^ m i) := by
      apply Nat.add_le_add
      · exact (weightedTotalDegree_C v r).le
      · exact AddMonoidAlgebra.supDegree_prod_le (R := R) (A := τ →₀ ℕ) (B := ℕ)
          (D := weight v) (map_zero (weight v))
          (fun a b => map_add (weight v) a b)
    _ ≤ ∑ i ∈ m.support, m i * weightedTotalDegree v (f i) := by
      simp only [zero_add]
      exact Finset.sum_le_sum fun i _ => weightedTotalDegree_pow_le v (f i) (m i)
    _ = weight (fun i => weightedTotalDegree v (f i)) m := by
      simp only [weight_apply, Finsupp.sum, smul_eq_mul]

/-- Substitution cannot exceed the outer polynomial's weighted degree when each source variable is
assigned the weighted total degree of its substituted polynomial. This induced-weight form has no
positivity or nonzero hypotheses and includes zero polynomials and zero substitutions. -/
theorem weightedTotalDegree_bind₁_le {τ : Type*} (v : τ → ℕ)
    (f : σ → MvPolynomial τ R) (p : MvPolynomial σ R) :
    weightedTotalDegree v (bind₁ f p) ≤
      weightedTotalDegree (fun i => weightedTotalDegree v (f i)) p := by
  conv_lhs => rw [p.as_sum, map_sum]
  calc
    weightedTotalDegree v (∑ m ∈ p.support, bind₁ f (monomial m (p.coeff m))) ≤
        p.support.sup fun m => weightedTotalDegree v (bind₁ f (monomial m (p.coeff m))) :=
      AddMonoidAlgebra.supDegree_sum_le
    _ ≤ p.support.sup fun m => weight (fun i => weightedTotalDegree v (f i)) m :=
      Finset.sup_mono_fun fun m _ =>
        weightedTotalDegree_bind₁_monomial_le v f m (p.coeff m)
    _ = weightedTotalDegree (fun i => weightedTotalDegree v (f i)) p := rfl

/-- Prescribed-weight substitution bound: if the image of source variable `i` has target weighted
degree at most `w i`, substitution does not increase the outer `w`-weighted total degree. -/
theorem weightedTotalDegree_bind₁_le_of_le {τ : Type*} (w : σ → ℕ) (v : τ → ℕ)
    (f : σ → MvPolynomial τ R) (p : MvPolynomial σ R)
    (hf : ∀ i, weightedTotalDegree v (f i) ≤ w i) :
    weightedTotalDegree v (bind₁ f p) ≤ weightedTotalDegree w p := by
  refine (weightedTotalDegree_bind₁_le v f p).trans ?_
  unfold weightedTotalDegree
  exact Finset.sup_mono_fun fun m _ => Finsupp.sum_le_sum fun i _ =>
    Nat.mul_le_mul_left (m i) (hf i)

/-- The prescribed-weight substitution bound through the standard `MvPolynomial.aeval`
spelling. -/
theorem weightedTotalDegree_aeval_le_of_le {τ : Type*} (w : σ → ℕ) (v : τ → ℕ)
    (f : σ → MvPolynomial τ R) (p : MvPolynomial σ R)
    (hf : ∀ i, weightedTotalDegree v (f i) ≤ w i) :
    weightedTotalDegree v (aeval f p) ≤ weightedTotalDegree w p := by
  rw [aeval_eq_bind₁]
  exact weightedTotalDegree_bind₁_le_of_le w v f p hf

/-! ### Partial derivatives -/

/-- A partial derivative in `X i` lowers the `w`-weighted total degree by at least `w i`.

Every monomial of `pderiv i p` comes from a monomial of `p` with one more factor `X i`, which
carries weight `w i`. This holds in every characteristic. Truncated subtraction covers the cases
`pderiv i p = 0` and `w i > weightedTotalDegree w p`; in the second case `p` has no monomial
containing `X i` and the derivative is zero. -/
theorem weightedTotalDegree_pderiv_le_sub (w : σ → ℕ) (i : σ) (p : MvPolynomial σ R) :
    weightedTotalDegree w (pderiv i p) ≤ weightedTotalDegree w p - w i := by
  rw [weightedTotalDegree, Finset.sup_le_iff]
  intro m hm
  have horig : p.coeff (m + Finsupp.single i 1) ≠ 0 := by
    intro hzero
    rw [mem_support_iff, coeff_pderiv, hzero, zero_mul] at hm
    exact hm rfl
  have h := le_weightedTotalDegree w (mem_support_iff.mpr horig)
  rw [map_add, weight_single, one_smul] at h
  omega

/-! ### Substitution of univariate polynomials -/

/-- Substituting univariate polynomials `f i` for the variables gives a univariate polynomial of
`natDegree` at most the weighted total degree of `p` for the weights `natDegree (f i)`.

This is the univariate-target analogue of `weightedTotalDegree_aeval_le`. It has no nonzero or
positivity hypotheses: constant substitutions receive weight zero, and `p = 0` has weighted total
degree zero. The inequality can be strict because leading coefficients can cancel. -/
theorem natDegree_aeval_le_weightedTotalDegree (f : σ → Polynomial R) (p : MvPolynomial σ R) :
    (aeval f p).natDegree ≤ weightedTotalDegree (fun i => (f i).natDegree) p := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => ?_
  rw [aeval_monomial, Polynomial.algebraMap_eq]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  refine le_trans ?_ (le_weightedTotalDegree _ hm)
  rw [weight_apply, Finsupp.sum]
  exact Finset.sum_le_sum fun i _ => by
    rw [smul_eq_mul]
    exact Polynomial.natDegree_pow_le

/-- If each substituted univariate polynomial satisfies `natDegree (f i) ≤ w i`, then
`natDegree (aeval f p)` is at most the `w`-weighted total degree of `p`.

This is the univariate-target analogue of `weightedTotalDegree_aeval_le_of_le`. Zero weights are
allowed; they force the corresponding `f i` to be constant. -/
theorem natDegree_aeval_le_weightedTotalDegree_of_le (w : σ → ℕ) (f : σ → Polynomial R)
    (p : MvPolynomial σ R) (hf : ∀ i, (f i).natDegree ≤ w i) :
    (aeval f p).natDegree ≤ weightedTotalDegree w p := by
  refine (natDegree_aeval_le_weightedTotalDegree f p).trans ?_
  unfold weightedTotalDegree
  exact Finset.sup_mono_fun fun m _ => Finsupp.sum_le_sum fun i _ =>
    Nat.mul_le_mul_left (m i) (hf i)

/-- The monomial basis restricted to exponents of weight at most `d`. -/
def basisRestrictWeightedDegree (w : σ → ℕ) (d : ℕ) :
    Basis {m : σ →₀ ℕ // m.weight w ≤ d} R (restrictWeightedDegree (R := R) w d) :=
  basisRestrictSupport R {m | m.weight w ≤ d}

/-- Coordinates in the restricted monomial basis are the ordinary polynomial coefficients. -/
@[simp]
theorem basisRestrictWeightedDegree_repr_apply (w : σ → ℕ) (d : ℕ)
    (p : restrictWeightedDegree (R := R) w d)
    (m : {m : σ →₀ ℕ // m.weight w ≤ d}) :
    (basisRestrictWeightedDegree (R := R) w d).repr p m =
      (p : MvPolynomial σ R).coeff m :=
  rfl

/-- Coefficient projection from a bounded weighted-degree submodule at an allowed monomial. -/
def restrictWeightedDegreeCoeff (w : σ → ℕ) (d : ℕ)
    (m : {m : σ →₀ ℕ // m.weight w ≤ d}) :
    restrictWeightedDegree (R := R) w d →ₗ[R] R :=
  lcoeff R m ∘ₗ Submodule.subtype _

@[simp]
theorem restrictWeightedDegreeCoeff_apply (w : σ → ℕ) (d : ℕ)
    (m : {m : σ →₀ ℕ // m.weight w ≤ d})
    (p : restrictWeightedDegree (R := R) w d) :
    restrictWeightedDegreeCoeff (R := R) w d m p =
      (p : MvPolynomial σ R).coeff m :=
  rfl

end MvPolynomial
