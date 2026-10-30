/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/Polynomial/TaylorPrefix.lean, commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence:
Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 7 of the 10 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
* Lemmas are called by their names in Lean 4.29.1 and this Mathlib: finsetSum_coeff became
  finset_sum_coeff (1 time); ite_eq_left became if_pos (3 times); ite_eq_right became if_neg (3
  times).
-/

import Mathlib.Algebra.Lie.OfAssociative
import ThirdParty.ArkLib.ToMathlib.Polynomial.HasseTaylor.FiniteJet

/-!
# Polynomials from finite Hasse--Taylor prefixes

This file constructs the unique degree-`< K` polynomial with prescribed first `K` Hasse
coefficients at a chosen center.  The construction translates an explicit coefficient polynomial
back from the displacement variable, and is valid over every commutative ring.  In particular, it
uses no factorial denominators or characteristic bounds.

The main declarations are:

* `Polynomial.centeredCoefficientPrefix`, the polynomial reconstructed from a finite coefficient
  prefix;
* `Polynomial.coeff_taylor_centeredCoefficientPrefix` and
  `Polynomial.hasseJet_centeredCoefficientPrefix`, its coefficient and finite-jet specifications;
* `Polynomial.degree_centeredCoefficientPrefix_lt`, its strict degree bound;
* `Polynomial.centeredCoefficientPrefix_succ`, the one-coefficient extension law.

The construction is independent of Reed--Solomon codes and differential root finding.
-/

open scoped BigOperators

namespace Polynomial

noncomputable section

variable {R : Type*} [CommRing R]

/-- The degree-`< K` polynomial whose first `K` Hasse coefficients at `center` are `c 0`, ...,
`c (K - 1)`.

The finite sum is first formed in the displacement variable and then translated back to the
original variable. -/
def centeredCoefficientPrefix (center : R) (c : ℕ → R) (K : ℕ) : R[X] :=
  taylor (-center) (∑ i : Fin K, monomial i.val (c i.val))

/-- Translating a centered coefficient prefix to the origin recovers its explicit monomial sum. -/
theorem taylor_centeredCoefficientPrefix (center : R) (c : ℕ → R) (K : ℕ) :
    taylor center (centeredCoefficientPrefix center c K) =
      ∑ i : Fin K, monomial i.val (c i.val) := by
  unfold centeredCoefficientPrefix
  rw [taylor_taylor, add_neg_cancel, taylor_zero]

/-- The translated prefix has exactly the prescribed coefficients below `K` and zero coefficients
at and above `K`. -/
theorem coeff_taylor_centeredCoefficientPrefix (center : R) (c : ℕ → R) (K i : ℕ) :
    (taylor center (centeredCoefficientPrefix center c K)).coeff i =
      if i < K then c i else 0 := by
  classical
  rw [taylor_centeredCoefficientPrefix, finset_sum_coeff]
  by_cases hi : i < K
  · rw [if_pos hi]
    rw [Finset.sum_eq_single (⟨i, hi⟩ : Fin K)]
    · simp
    · intro j _ hj
      rw [coeff_monomial, if_neg]
      exact fun h ↦ hj (Fin.ext h)
    · simp
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro j _
    rw [coeff_monomial, if_neg]
    intro h
    exact hi (h ▸ j.isLt)

/-- The order-`K` Hasse jet of a length-`K` prefix is its prescribed coefficient vector. -/
@[simp]
theorem hasseJet_centeredCoefficientPrefix (center : R) (c : ℕ → R) (K : ℕ) :
    hasseJet K center (centeredCoefficientPrefix center c K) = fun i ↦ c i.val := by
  funext i
  rw [hasseJet_eq_taylor_coeff, coeff_taylor_centeredCoefficientPrefix, if_pos i.isLt]

/-- Every shorter Hasse jet of a centered coefficient prefix is the corresponding initial segment
of its prescribed coefficients. -/
theorem hasseJet_centeredCoefficientPrefix_of_le (center : R) (c : ℕ → R) {m K : ℕ}
    (hmK : m ≤ K) :
    hasseJet m center (centeredCoefficientPrefix center c K) = fun i ↦ c i.val := by
  funext i
  rw [hasseJet_eq_taylor_coeff, coeff_taylor_centeredCoefficientPrefix,
    if_pos (i.isLt.trans_le hmK)]

/-- The empty centered coefficient prefix is the zero polynomial. -/
@[simp]
theorem centeredCoefficientPrefix_zero (center : R) (c : ℕ → R) :
    centeredCoefficientPrefix center c 0 = 0 := by
  simp [centeredCoefficientPrefix]

/-- Appending one coefficient adds the corresponding power of `X - center`. -/
theorem centeredCoefficientPrefix_succ (center : R) (c : ℕ → R) (K : ℕ) :
    centeredCoefficientPrefix center c (K + 1) =
      centeredCoefficientPrefix center c K + C (c K) * (X - C center) ^ K := by
  apply taylor_injective center
  rw [map_add, taylor_centeredCoefficientPrefix, taylor_centeredCoefficientPrefix,
    Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_last]
  congr 1
  rw [taylor_mul, taylor_C, taylor_pow]
  simp [taylor_X, C_mul_X_pow_eq_monomial]

end

end Polynomial
