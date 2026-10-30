/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/MvPolynomial/WeightedOrder.lean, commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13.
Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 10 of the 20 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Data.Finsupp.Weight
import Mathlib.GroupTheory.GroupAction.Ring
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Weighted-order bounds and weighted truncation of multivariate polynomials

For a weight `w : σ → ℕ`, this file studies lower bounds on the weights of monomials, the
counterpart of the upper bounds in `ArkLib.Data.MvPolynomial.WeightedDegree`.

* `restrictWeightedOrder w m` is the submodule of polynomials each of whose monomials has
  `w`-weight at least `m`. It contains the zero polynomial for every `m`, and every polynomial
  when `m = 0`.
* `filterSupport p` keeps exactly the monomials whose exponents satisfy `p`, and
  `weightedTruncation w m` is the special case keeping the monomials of weight below `m`.

The main result, `weightedTruncation_bind₁_weightedTruncation`, says that truncation commutes
with a substitution that does not lower weights: if every generator image `f i` has all of its
monomials of `v`-weight at least `w i`, then truncating the input below `w`-weight `m` does not
change the output truncated below `v`-weight `m`. No hypothesis on the coefficient ring is
needed.

## Main statements

* `bind₁_mem_restrictWeightedOrder`: substitution preserves weighted-order lower bounds.
* `pow_dvd_eval₂Hom_of_mem_restrictWeightedOrder`: evaluating a polynomial of weighted order at
  least `m` at values `g i` divisible by `t ^ (w i)` gives a value divisible by `t ^ m`.
* `weightedTruncation_eq_zero_iff`: a truncation vanishes exactly on the corresponding
  weighted-order submodule.
* `weightedTruncation_bind₁_weightedTruncation`: truncation commutes with weight-nondecreasing
  substitution.

Parts of this file are adapted, with permission, from Kai Zhe Zheng's `kz99/rs-ld-mca`
formalization.
-/

noncomputable section

open Finsupp
open scoped Pointwise

namespace MvPolynomial

variable {σ τ R : Type*} [CommSemiring R]

/-! ### Weighted-order submodules -/

/-- The polynomials all of whose monomials have `w`-weight at least `m`. -/
def restrictWeightedOrder (w : σ → ℕ) (m : ℕ) : Submodule R (MvPolynomial σ R) :=
  restrictSupport R {e | m ≤ e.weight w}

/-- Membership in `restrictWeightedOrder` is the pointwise lower bound on the support. -/
theorem mem_restrictWeightedOrder {w : σ → ℕ} {m : ℕ} {p : MvPolynomial σ R} :
    p ∈ restrictWeightedOrder (R := R) w m ↔ ∀ e ∈ p.support, m ≤ e.weight w :=
  Iff.rfl

/-- Every polynomial satisfies the lower bound zero. -/
@[simp]
theorem restrictWeightedOrder_zero (w : σ → ℕ) :
    restrictWeightedOrder (R := R) w 0 = ⊤ := by
  ext p
  simp [mem_restrictWeightedOrder]

/-- A monomial satisfies the lower bound exactly when its exponent does, unless its coefficient
is zero. -/
@[simp]
theorem monomial_mem_restrictWeightedOrder (w : σ → ℕ) (m : ℕ) (e : σ →₀ ℕ) (r : R) :
    monomial e r ∈ restrictWeightedOrder (R := R) w m ↔ m ≤ e.weight w ∨ r = 0 :=
  monomial_mem_restrictSupport (R := R) (s := {e | m ≤ e.weight w})

/-- Evaluation of a polynomial of weighted order at least `m`. If `t ^ (w i)` divides the value
`g i` of every variable `i`, then `t ^ m` divides `p(g)`: each monomial `x^e` of `p` has
`w`-weight at least `m`, and its value is divisible by `t` to the power of that weight. Variables
of weight zero impose no condition. -/
theorem pow_dvd_eval₂Hom_of_mem_restrictWeightedOrder {S : Type*} [CommSemiring S]
    (f : R →+* S) {g : σ → S} {t : S} {w : σ → ℕ} {m : ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ restrictWeightedOrder (R := R) w m) (hg : ∀ i, t ^ w i ∣ g i) :
    t ^ m ∣ eval₂Hom f g p := by
  rw [p.as_sum, map_sum]
  refine Finset.dvd_sum fun e he => ?_
  rw [eval₂Hom_monomial]
  refine (pow_dvd_pow t (mem_restrictWeightedOrder.mp hp e he)).trans (Dvd.dvd.mul_left ?_ _)
  rw [weight_apply, Finsupp.sum, Finsupp.prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun i _ => ?_
  rw [smul_eq_mul, mul_comm, pow_mul]
  exact pow_dvd_pow_of_dvd (hg i) _

/-! ### Support filters and weighted truncation -/

/-- Coefficientwise projection onto the monomials whose exponents satisfy `p`. -/
def filterSupport (p : (σ →₀ ℕ) → Prop) [DecidablePred p] :
    MvPolynomial σ R →ₗ[R] MvPolynomial σ R where
  toFun F := AddMonoidAlgebra.ofCoeff (Finsupp.filter p (AddMonoidAlgebra.coeff F))
  map_add' F G := by
    apply AddMonoidAlgebra.coeff_injective
    exact Finsupp.filter_add
  map_smul' a F := by
    apply AddMonoidAlgebra.coeff_injective
    exact Finsupp.filter_smul

/-- The coefficient of `filterSupport p F` at `e` is `F.coeff e` if `p e` holds and `0`
otherwise. -/
@[simp]
theorem coeff_filterSupport (p : (σ →₀ ℕ) → Prop) [DecidablePred p]
    (F : MvPolynomial σ R) (e : σ →₀ ℕ) :
    (filterSupport (R := R) p F).coeff e = if p e then F.coeff e else 0 :=
  Finsupp.filter_apply _ _ _

/-- A filtered polynomial vanishes exactly when every retained coefficient vanishes. -/
theorem filterSupport_eq_zero_iff (p : (σ →₀ ℕ) → Prop) [DecidablePred p]
    (F : MvPolynomial σ R) :
    filterSupport (R := R) p F = 0 ↔ ∀ e, p e → F.coeff e = 0 := by
  constructor
  · intro h e he
    simpa [he] using congrArg (fun G : MvPolynomial σ R => G.coeff e) h
  · intro h
    ext e
    by_cases he : p e <;> simp [he, h]

/-- Truncation below `w`-weight `m`: keep exactly the monomials of weight less than `m`. -/
def weightedTruncation (w : σ → ℕ) (m : ℕ) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  filterSupport fun e => e.weight w < m

/-- The coefficient of `weightedTruncation w m F` at `e` is `F.coeff e` if `e` has `w`-weight
below `m` and `0` otherwise. -/
@[simp]
theorem coeff_weightedTruncation (w : σ → ℕ) (m : ℕ) (F : MvPolynomial σ R)
    (e : σ →₀ ℕ) :
    (weightedTruncation (R := R) w m F).coeff e =
      if e.weight w < m then F.coeff e else 0 :=
  coeff_filterSupport _ F e

end MvPolynomial
