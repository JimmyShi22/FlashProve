/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/Polynomial/Differential/OrderZeroPresentation.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 1 of the 7 declarations of the file is kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.Data.Polynomial.Differential.TaylorResidual

/-!
# Order-zero differential polynomial presentation

This module converts between an order-zero differential polynomial and a univariate polynomial
in `Y₀` over `F[X]`, preserving total jet degree and differential specialization.

## Main statements

* `jetTotalDegree_eq_jetDegree_zero`: total jet degree is the degree in the only jet variable.
* `orderZeroAsPolynomial` and `orderZeroOfPolynomial`: the two polynomial presentations.
* `orderZeroOfPolynomial_jetTotalDegree` and `orderZeroAsPolynomial_eval`: degree and evaluation
  laws for the conversion.

## References

* [DKT26]
-/

noncomputable section

namespace PolynomialDifferential

open Polynomial MvPolynomial

universe u

variable {F : Type u} [CommSemiring F]

/-- For an order-zero differential polynomial, total jet degree is its degree in `Y₀`. -/
theorem jetTotalDegree_eq_jetDegree_zero (Q : DifferentialPolynomial F 0) :
    jetTotalDegree Q = jetDegree Q 0 := by
  classical
  rw [jetTotalDegree, jetDegree,
    ← MvPolynomial.weightedTotalDegree_piSingle (some (0 : Fin 1))]
  congr 1
  funext i
  cases i with
  | none => simp [jetDegreeWeight]
  | some j =>
    fin_cases j
    simp [jetDegreeWeight]

end PolynomialDifferential
