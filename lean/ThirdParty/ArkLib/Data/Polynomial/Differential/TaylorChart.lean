/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/Polynomial/Differential/TaylorChart.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 16 of the 25 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
* Lemmas are called by their names in Lean 4.29.1 and this Mathlib: eval_finsetSum became
  eval_finset_sum (1 time).
* Proof changed, aeval_commonTaylorNumerator: one line `have hp : … ^ (2 * (l - r) - 1) ≠ 0 :=
  pow_ne_zero _ hS` added before field_simp: this Mathlib's field_simp does not find that the power
  with a variable exponent is nonzero.
-/

import Mathlib.LinearAlgebra.Lagrange
import ThirdParty.ArkLib.Data.Polynomial.Differential.RationalTaylorAlgebra

/-!
# The rational Taylor chart of a differential equation

Let `Q` be a differential polynomial of order `r` over a field, fix a center `a`, and write `S`
for the separant at the initial jet (`initialJetSeparant a Q`) and `v = jetTotalDegree Q`. On the
open set `S ≠ 0` of initial jets `(c₀, ..., c_r)`, the rational Taylor coefficients
`c_l = rationalTaylorNumerator a Q l / S ^ (2(l - r) - 1)` parametrize the polynomial solutions of
`Q = 0` by their initial jets. This file clears all denominators of a length-`K` prefix at once.

For a common exponent `τ ≥ 2(l - r) - 1`, the polynomial
`commonTaylorNumerator a Q τ l = rationalTaylorNumerator a Q l * S ^ (τ - (2(l - r) - 1))`
evaluates to `S ^ τ * c_l` wherever `S ≠ 0`, and has total degree at most `1 + τ (v - 1)`. The
predicate `TaylorExponentSufficient r K τ` says that `τ` works for every `l < K`; the exponent
`2K` always does.

From these numerators the file builds three kinds of polynomial equations on the chart:

* the initial equation `initialJetEquation a Q`, which is `Q` with `X` set to `a`; every
  polynomial solution starts on it, and its derivative in the last jet coordinate is `S`;
* the high cuts `commonTaylorNumerator a Q τ l = 0` for `k ≤ l < K`, which force the
  reconstructed polynomial to have degree below `k`;
* the agreement equations `taylorAgreementEquation a Q K τ x y`, which after clearing `S ^ τ` say
  that the reconstructed polynomial takes the value `y` at `x`.

The reconstructed polynomial `rationalTaylorPolynomial a Q K jet` has the first `K` rational
coefficients as its Taylor coefficients at `a`. It keeps the initial jet when `r < K`, and it is
the solution itself at the jet of a solution of degree below `K` whose separant and binomial
pivots `(i choose r)`, `r < i < K`, are nonzero. Consequently, on `S ≠ 0`, the high cuts and
agreement with `k` distinct points determine the initial jet.

## Main statements

* The initial equation specialization and its basic laws come from `JetDegree`;
  `pderiv_last_initialJetEquation` and `aeval_initialJetEquation_polynomialJet` give the initial
  separant and polynomial-solution consequences for the chart.
* `commonTaylorNumerator`, `totalDegree_commonTaylorNumerator_le` and
  `aeval_commonTaylorNumerator`: the cleared coefficients and their degree bound
  `rationalTaylorCutDegreeBound Q τ = 1 + τ (v - 1)`.
* `commonTaylorNumeratorOver_eq` and `map_commonTaylorNumeratorOver_eq`: field specialization of
  the algebra-valued common numerator, the latter along any `F`-algebra map.
* `aeval_commonTaylorNumerator_eq_zero`: on `S ≠ 0`, a vanishing coefficient makes its common
  numerator vanish for every exponent.
* `rationalTaylorMap_injective` and `rationalTaylorMap_polynomialJet`: the chart keeps the initial
  coordinates and contains every regular solution.
* `taylorAgreementEquation`, `totalDegree_taylorAgreementEquation_le`,
  `aeval_taylorAgreementEquation` and `taylorAgreementEquation_eq_zero_iff`: agreement equations.
* `rationalTaylorPolynomial_polynomialJet`: the reconstruction of a regular solution is the
  solution.
* `degree_rationalTaylorPolynomial_lt`: the high cuts bound the degree of the reconstruction.
* `eq_of_highTaylorCuts_of_agreement`: on `S ≠ 0`, the high cuts and `k` agreement equations at
  distinct points leave at most one initial jet.

## References

* [DKT26]
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial
open scoped BigOperators

/-! ### The initial hypersurface -/

section CommSemiring

variable {R : Type*} [CommSemiring R] {r : ℕ}

/-- The partial derivative of the initial equation in the last jet coordinate is the initial
separant. -/
theorem pderiv_last_initialJetEquation (center : R) (Q : DifferentialPolynomial R r) :
    pderiv (Fin.last r) (initialJetEquation center Q) = initialJetSeparant center Q :=
  pderiv_initialJetEquation center Q (Fin.last r)

/-- A nonzero initial separant forces the initial equation to be nonzero. -/
theorem initialJetEquation_ne_zero_of_initialJetSeparant_ne_zero (center : R)
    (Q : DifferentialPolynomial R r) (hS : initialJetSeparant center Q ≠ 0) :
    initialJetEquation center Q ≠ 0 := by
  intro h
  apply hS
  rw [← pderiv_last_initialJetEquation, h, map_zero]

/-- The Hasse jet of every polynomial solution of `Q = 0` lies on the initial hypersurface. -/
theorem aeval_initialJetEquation_polynomialJet (center : R) (Q : DifferentialPolynomial R r)
    (P : Polynomial R) (hsolution : differentialSpecialization Q P = 0) :
    aeval (polynomialJet center P) (initialJetEquation center Q) = 0 := by
  rw [aeval_initialJetEquation, ← eval_differentialSpecialization, hsolution,
    Polynomial.eval_zero]

end CommSemiring

/-! ### Common-denominator numerators -/

variable {F : Type*} [Field F] {r : ℕ}

/-- The numerator of the rational Taylor coefficient `c_l` over the common denominator `S ^ τ`,
where `S` is the initial separant: `rationalTaylorNumerator center Q l * S ^ (τ - (2(l - r) - 1))`.
It represents `S ^ τ * c_l` when `2(l - r) - 1 ≤ τ`. -/
def commonTaylorNumerator (center : F) (Q : DifferentialPolynomial F r) (τ l : ℕ) :
    MvPolynomial (Fin (r + 1)) F :=
  rationalTaylorNumerator center Q l * initialJetSeparant center Q ^ (τ - (2 * (l - r) - 1))

/-- Over a field containing `F`, the common numerator over an `F`-algebra equals the field
common numerator. -/
theorem commonTaylorNumeratorOver_eq {E : Type*} [Field E] [Algebra F E]
    (center : E) (Q : DifferentialPolynomial E r) (τ l : ℕ) :
    commonTaylorNumeratorOver F center Q τ l = commonTaylorNumerator center Q τ l := by
  rw [commonTaylorNumeratorOver, commonTaylorNumerator, rationalTaylorNumeratorOver_eq]

/-- Mapping an algebra-valued common numerator into a field gives the common numerator of the
mapped equation. -/
theorem map_commonTaylorNumeratorOver_eq {A E : Type*} [CommRing A] [Algebra F A]
    [Field E] [Algebra F E] (φ : A →ₐ[F] E) (center : A)
    (Q : DifferentialPolynomial A r) (τ l : ℕ) :
    map φ.toRingHom (commonTaylorNumeratorOver F center Q τ l) =
      commonTaylorNumerator (φ center) (map φ.toRingHom Q) τ l := by
  rw [map_commonTaylorNumeratorOver, commonTaylorNumeratorOver_eq]

/-- If `2(l - r) - 1 ≤ τ` and the separant `S` does not vanish at `jet`, the common numerator
evaluates to `S ^ τ * c_l`. The separant hypothesis is needed when `τ = 2(l - r) - 1 > 0`: then
the rational coefficient is `0` at `S = 0` by the convention on division by zero, while the
numerator need not vanish. -/
theorem aeval_commonTaylorNumerator (center : F) (Q : DifferentialPolynomial F r)
    (jet : Fin (r + 1) → F) {τ l : ℕ} (hl : 2 * (l - r) - 1 ≤ τ)
    (hS : aeval jet (initialJetSeparant center Q) ≠ 0) :
    aeval jet (commonTaylorNumerator center Q τ l) =
      aeval jet (initialJetSeparant center Q) ^ τ * rationalTaylorCoefficient center Q jet l := by
  rw [commonTaylorNumerator, map_mul, map_pow, rationalTaylorCoefficient]
  have he : aeval jet (initialJetSeparant center Q) ^ τ =
      aeval jet (initialJetSeparant center Q) ^ (τ - (2 * (l - r) - 1)) *
        aeval jet (initialJetSeparant center Q) ^ (2 * (l - r) - 1) := by
    rw [← pow_add, Nat.sub_add_cancel hl]
  rw [he]
  have hp : aeval jet (initialJetSeparant center Q) ^ (2 * (l - r) - 1) ≠ 0 := pow_ne_zero _ hS
  field_simp

private theorem aeval_commonTaylorNumerator_eq_zero_iff (center : F)
    (Q : DifferentialPolynomial F r)
    (jet : Fin (r + 1) → F) {τ l : ℕ} (hl : 2 * (l - r) - 1 ≤ τ)
    (hS : aeval jet (initialJetSeparant center Q) ≠ 0) :
    aeval jet (commonTaylorNumerator center Q τ l) = 0 ↔
      rationalTaylorCoefficient center Q jet l = 0 := by
  rw [aeval_commonTaylorNumerator center Q jet hl hS, mul_eq_zero,
    or_iff_right (pow_ne_zero _ hS)]

/-! ### The rational Taylor map -/

/-! ### The reconstructed polynomial -/

/-- The polynomial of degree below `K` whose Taylor coefficients at `center` are the first `K`
rational Taylor coefficients of `jet`. -/
def rationalTaylorPolynomial (center : F) (Q : DifferentialPolynomial F r) (K : ℕ)
    (jet : Fin (r + 1) → F) : Polynomial F :=
  Polynomial.centeredCoefficientPrefix center (rationalTaylorCoefficient center Q jet) K

/-- The reconstruction evaluates at `x` to `∑_{l < K} c_l (x - center) ^ l`. -/
theorem eval_rationalTaylorPolynomial (center : F) (Q : DifferentialPolynomial F r) (K : ℕ)
    (jet : Fin (r + 1) → F) (x : F) :
    (rationalTaylorPolynomial center Q K jet).eval x =
      ∑ l : Fin K, rationalTaylorCoefficient center Q jet l.val * (x - center) ^ l.val := by
  have he := congrArg (fun p : Polynomial F ↦ p.eval (x - center))
    (Polynomial.taylor_centeredCoefficientPrefix center (rationalTaylorCoefficient center Q jet) K)
  simpa [rationalTaylorPolynomial, Polynomial.eval_finset_sum, Polynomial.eval_monomial,
    Polynomial.taylor_eval] using he

/-- For `r < K`, the reconstruction has the initial jet `jet`. -/
theorem polynomialJet_rationalTaylorPolynomial (center : F) (Q : DifferentialPolynomial F r)
    {K : ℕ} (hK : r < K) (jet : Fin (r + 1) → F) :
    polynomialJet (d := r) center (rationalTaylorPolynomial center Q K jet) = jet := by
  rw [rationalTaylorPolynomial, polynomialJet,
    Polynomial.hasseJet_centeredCoefficientPrefix_of_le center _ (by omega : r + 1 ≤ K)]
  funext j
  exact rationalTaylorCoefficient_initial center Q jet j

/-- The reconstruction at the Hasse jet of a polynomial solution `P` of degree below `K` is `P`,
provided the separant at the jet and the binomial pivots `(i choose r)` for `r < i < K` are
nonzero. -/
theorem rationalTaylorPolynomial_polynomialJet (center : F) (Q : DifferentialPolynomial F r)
    (P : Polynomial F) (hsolution : differentialSpecialization Q P = 0)
    (hseparant : jetEvaluation (separant Q (Fin.last r)) center (polynomialJet center P) ≠ 0)
    {K : ℕ} (hP : P.degree < K) (hbin : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0) :
    rationalTaylorPolynomial center Q K (polynomialJet center P) = P := by
  apply Polynomial.taylor_injective center
  ext i
  rw [rationalTaylorPolynomial, Polynomial.coeff_taylor_centeredCoefficientPrefix]
  split_ifs with hi
  · exact rationalTaylorCoefficient_eq_solution center Q P hsolution hseparant i
      (fun j hj hji ↦ hbin j hj (hji.trans_lt hi))
  · refine (Polynomial.coeff_eq_zero_of_degree_lt ?_).symm
    rw [Polynomial.degree_taylor]
    exact hP.trans_le (by exact_mod_cast not_lt.mp hi)

/-- On `S ≠ 0`, if the common numerators of `c_l` vanish for `k ≤ l < K`, the reconstruction has
degree below `k`. -/
theorem degree_rationalTaylorPolynomial_lt (center : F) (Q : DifferentialPolynomial F r)
    {K τ : ℕ} (hτ : TaylorExponentSufficient r K τ) (k : ℕ) (jet : Fin (r + 1) → F)
    (hS : aeval jet (initialJetSeparant center Q) ≠ 0)
    (hhigh : ∀ l, k ≤ l → l < K → aeval jet (commonTaylorNumerator center Q τ l) = 0) :
    (rationalTaylorPolynomial center Q K jet).degree < k := by
  rw [← Polynomial.degree_taylor _ center, Polynomial.degree_lt_iff_coeff_zero]
  intro i hi
  rw [rationalTaylorPolynomial, Polynomial.coeff_taylor_centeredCoefficientPrefix]
  split_ifs with hiK
  · exact (aeval_commonTaylorNumerator_eq_zero_iff center Q jet (hτ ⟨i, hiK⟩) hS).mp
      (hhigh i (by exact_mod_cast hi) hiK)
  · rfl

/-! ### Agreement equations -/

/-- The agreement equation at `x` with value `y`: the equation
`∑_{l < K} (x - center) ^ l * N_l - y * S ^ τ = 0` in the initial jet, where `N_l` is the common
numerator of `c_l` with exponent `τ` and `S` is the initial separant. On `S ≠ 0` it says that the
reconstructed polynomial takes the value `y` at `x`. -/
def taylorAgreementEquation (center : F) (Q : DifferentialPolynomial F r) (K τ : ℕ) (x y : F) :
    MvPolynomial (Fin (r + 1)) F :=
  (∑ l : Fin K, C ((x - center) ^ l.val) * commonTaylorNumerator center Q τ l.val) -
    C y * initialJetSeparant center Q ^ τ

/-- For a sufficient exponent and `S ≠ 0`, the agreement equation evaluates to `S ^ τ` times the
discrepancy of the reconstructed polynomial at `x` from `y`. -/
theorem aeval_taylorAgreementEquation (center : F) (Q : DifferentialPolynomial F r)
    {K τ : ℕ} (hτ : TaylorExponentSufficient r K τ) (jet : Fin (r + 1) → F)
    (hS : aeval jet (initialJetSeparant center Q) ≠ 0) (x y : F) :
    aeval jet (taylorAgreementEquation center Q K τ x y) =
      aeval jet (initialJetSeparant center Q) ^ τ *
        ((rationalTaylorPolynomial center Q K jet).eval x - y) := by
  rw [taylorAgreementEquation, map_sub, map_sum, eval_rationalTaylorPolynomial, mul_sub,
    Finset.mul_sum]
  simp only [map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, map_pow]
  congr 1
  · refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [aeval_commonTaylorNumerator center Q jet (hτ l) hS]
    ring
  · ring

/-- For a sufficient exponent and `S ≠ 0`, the agreement equation at `(x, y)` vanishes exactly
when the reconstructed polynomial takes the value `y` at `x`. -/
theorem taylorAgreementEquation_eq_zero_iff (center : F) (Q : DifferentialPolynomial F r)
    {K τ : ℕ} (hτ : TaylorExponentSufficient r K τ) (jet : Fin (r + 1) → F)
    (hS : aeval jet (initialJetSeparant center Q) ≠ 0) (x y : F) :
    aeval jet (taylorAgreementEquation center Q K τ x y) = 0 ↔
      (rationalTaylorPolynomial center Q K jet).eval x = y := by
  rw [aeval_taylorAgreementEquation center Q hτ jet hS x y, mul_eq_zero,
    or_iff_right (pow_ne_zero _ hS), sub_eq_zero]

/-! ### Uniqueness from high cuts and agreement -/

end

end PolynomialDifferential
