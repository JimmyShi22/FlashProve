/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/ToMathlib/Polynomial/HasseTaylor/Lifting.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 7 of the 17 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import Mathlib.Data.Nat.Choose.Dvd
import ThirdParty.ArkLib.ToMathlib.Polynomial.HasseTaylor.Shift

/-!
# Hasse--Taylor coefficient perturbations

Adding `γ * (X - a) ^ i` to a polynomial changes exactly its Hasse coefficient of order `i` at
`a`. After taking the Hasse derivative of order `s ≤ i`, the first changed coefficient has order
`i - s` and changes by `(i choose s) * γ`. So when `(i choose s)` is a unit, there is exactly one
`γ` that gives that coefficient a prescribed value.

These are the univariate facts behind the regular power-series lift of [Kop15, Theorem 4.4]; the
multivariate step is `PolynomialDifferential.existsUnique_regularLiftCoefficient`. Everything
holds over a commutative ring. The only arithmetic input is that the binomial coefficient is a
unit, or nonzero in a field; `natCast_choose_ne_zero_of_lt_charP` supplies this below a prime
characteristic.

## Main statements

* `Polynomial.hassePerturbation`: the polynomial `C γ * (X - C a) ^ i`.
* `Polynomial.hasseCoeffAt_hassePerturbation`: it has exactly one nonzero Hasse coefficient at
  `a`.
* `Polynomial.hasseDeriv_hassePerturbation`: its Hasse derivative of order `s` is the
  perturbation of order `i - s` with coefficient `(i choose s) * γ`.
* `Polynomial.hasseCoeffAt_hasseDeriv_add_hassePerturbation`: the first exposed coefficient after
  differentiation changes by `(i choose s) * γ`, and
  `hasseCoeffAt_hasseDeriv_add_hassePerturbation_of_lt`: lower coefficients do not change.
* `Polynomial.existsUnique_hasseCoeffAt_hasseDeriv_add_hassePerturbation_eq`: unique choice of
  `γ` when `(i choose s)` is a unit.
* `Polynomial.natCast_choose_ne_zero_of_lt_charP`: `(i choose s) ≠ 0` below a prime
  characteristic.
* `Polynomial.X_pow_dvd_taylor_hasseDeriv_sub_of_X_pow_add_dvd`: agreement to centered order
  `m + s` gives agreement of Hasse derivatives of order `s` to centered order `m`.
* `Polynomial.X_pow_dvd_taylor_iff_X_sub_C_pow_dvd` and
  `X_pow_succ_dvd_iff_coeff_eq_zero_of_X_pow_dvd`: divisibility bookkeeping used by the lift.

## References

* [Kopparty, S., *List-Decoding Multiplicity Codes*][Kop15], Definition 2.1 and Theorem 4.4.
-/

namespace Polynomial

noncomputable section

variable {R : Type*}

section CommRing

variable [CommRing R]

/-! ### A single centered coefficient perturbation -/

/-- The polynomial `γ * (X - a) ^ i`: in coordinates centered at `a`, the single monomial of
degree `i` with coefficient `γ`. -/
def hassePerturbation (a γ : R) (i : ℕ) : R[X] :=
  C γ * (X - C a) ^ i

/-- Translating a centered perturbation to the origin gives the monomial `γ * X ^ i`. -/
@[simp]
theorem taylor_hassePerturbation (a γ : R) (i : ℕ) :
    taylor a (hassePerturbation a γ i) = C γ * X ^ i := by
  simp [hassePerturbation, taylor_apply]

/-- A centered perturbation has exactly one nonzero Hasse coefficient at its center. -/
@[simp]
theorem hasseCoeffAt_hassePerturbation (a γ : R) (i j : ℕ) :
    hasseCoeffAt a j (hassePerturbation a γ i) = if j = i then γ else 0 := by
  rw [hasseCoeffAt_apply, ← taylor_coeff, taylor_hassePerturbation, coeff_C_mul, coeff_X_pow]
  split_ifs <;> simp

/-! ### Effect of Hasse differentiation -/

/-- The Hasse derivative of order `s` of `γ * (X - a) ^ i` is
`(i choose s) * γ * (X - a) ^ (i - s)`. For `s > i` both sides are zero, since
`i choose s = 0`. -/
theorem hasseDeriv_hassePerturbation (a γ : R) (i s : ℕ) :
    hasseDeriv s (hassePerturbation a γ i) =
      hassePerturbation a ((i.choose s : R) * γ) (i - s) := by
  apply taylor_injective a
  rw [← hasseDeriv_taylor, taylor_hassePerturbation, taylor_hassePerturbation]
  simp only [C_mul_X_pow_eq_monomial, hasseDeriv_monomial]

/-- `hasseDeriv_hassePerturbation` after adding the perturbation to a polynomial `p`. -/
theorem hasseDeriv_add_hassePerturbation (p : R[X]) (a γ : R) (i s : ℕ) :
    hasseDeriv s (p + hassePerturbation a γ i) =
      hasseDeriv s p + hassePerturbation a ((i.choose s : R) * γ) (i - s) := by
  rw [LinearMap.map_add, hasseDeriv_hassePerturbation]

/-! ### Unique choice of the perturbation coefficient -/

/-! ### Centered divisibility and agreement to finite order -/

/-- Divisibility by `(X - a) ^ m` is divisibility of the Taylor expansion at `a` by `X ^ m`. -/
theorem X_pow_dvd_taylor_iff_X_sub_C_pow_dvd (p : R[X]) (a : R) (m : ℕ) :
    X ^ m ∣ taylor a p ↔ (X - C a) ^ m ∣ p := by
  rw [X_sub_C_pow_dvd_iff, taylor_apply]

/-- If the Taylor expansions of `p` and `q` at `a` agree below order `m + s`, then those of their
Hasse derivatives of order `s` agree below order `m`. Equivalently, `(X - a) ^ (m + s) ∣ p - q`
implies `(X - a) ^ m ∣ Dˢp - Dˢq`. -/
theorem X_pow_dvd_taylor_hasseDeriv_sub_of_X_pow_add_dvd (p q : R[X]) (a : R) (m s : ℕ)
    (h : X ^ (m + s) ∣ taylor a p - taylor a q) :
    X ^ m ∣ taylor a (hasseDeriv s p) - taylor a (hasseDeriv s q) := by
  rw [← LinearMap.map_sub] at h
  rw [← LinearMap.map_sub, ← LinearMap.map_sub, ← hasseDeriv_taylor, X_pow_dvd_iff]
  intro i hi
  rw [hasseDeriv_coeff, X_pow_dvd_iff.mp h (i + s) (by omega), mul_zero]

end CommRing

section Semiring

variable [Semiring R]

end Semiring

section AddMonoidWithOne

variable [AddMonoidWithOne R]

/-! ### Binomial coefficients below a prime characteristic -/

end AddMonoidWithOne

end

end Polynomial
