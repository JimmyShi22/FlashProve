/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Global/Multiplicity.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 1 of the 2 declarations of the file is kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Contact
import ThirdParty.ArkLib.ToMathlib.Polynomial.RootMultiplicity

/-!
# Global vanishing of interpolation polynomials at agreeing polynomials

Let `Q` be in the exact interpolation space and satisfy the local constraints of order `m` at every
evaluation point `(points i, received i)`. If `P` has degree at most `D` and agrees with the
received word at `A` indices with distinct evaluation points, then `Q(X, P, D¹P, ..., DᵈP) = 0`.

Each agreement gives `(X - points i) ^ m ∣ Q(X, P, ...)`
(`X_sub_C_pow_dvd_differentialSpecialization_of_contact`), the specialization has degree below
`m * A` (`natDegree_differentialSpecialization_lt_of_mem_exactInterpolationSpace`), and a
polynomial over a domain with `A` distinct roots of multiplicity `m` and degree below `m * A` is
zero (`Polynomial.eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn`).

The same argument works with any `Q` whose weighted degree `differentialWeightedDegree D Q` is
below `m * A`, bounding the specialization's degree by `natDegree_differentialSpecialization_le`
instead of by membership in the exact space.

## Main statements

* `differentialSpecialization_eq_zero_of_mem_exactInterpolationSpace_of_agreements`.
* `differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt`: the weighted-degree form.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26], Section 3.3, and Section 3.6, Proposition 3.10
-/

open PolynomialDifferential Polynomial

namespace ReedSolomon.HiddenDerivative

variable {ι R : Type*} [CommRing R] [IsDomain R] {D A d m M W : ℕ}

/-- Let `Q` have weighted degree `differentialWeightedDegree D Q < m * A` and satisfy the local
constraints of order `m` at `(points i, received i)` for every `i` in `indices`. If `P` has degree
at most `D`, `P (points i) = received i` for every `i` in `indices`, the points are distinct on
`indices` and `A ≤ #indices`, then `Q(X, P, D¹P, ..., DᵈP) = 0`.

Each agreement gives `(X - points i) ^ m ∣ Q(X, P, ...)`, and the specialization has degree at most
the weighted degree, hence below `m * A`. The degree bound on `P` is needed because the weights
`differentialWeight D` bound the degrees of `P` and its Hasse derivatives only when
`P.natDegree ≤ D`. The domain hypothesis is used only in the final root count. -/
theorem differentialSpecialization_eq_zero_of_differentialWeightedDegree_lt
    (points received : ι → R) (indices : Finset ι) {Q : DifferentialPolynomial R d}
    (hdegree : differentialWeightedDegree D Q < m * A)
    (hconstraints : ∀ i ∈ indices, SatisfiesLocalConstraints m (points i) (received i) Q)
    (P : R[X]) (hPdegree : P.natDegree ≤ D) (hpoints : Set.InjOn points (indices : Set ι))
    (hcard : A ≤ indices.card) (hagreements : ∀ i ∈ indices, P.eval (points i) = received i) :
    differentialSpecialization Q P = 0 :=
  eq_zero_of_natDegree_lt_mul_of_pow_X_sub_C_dvd_at_injOn points indices m A hpoints hcard
    (fun i hi ↦ X_sub_C_pow_dvd_differentialSpecialization_of_contact Q P (points i) (received i)
      (hagreements i hi) (hconstraints i hi))
    ((natDegree_differentialSpecialization_le Q P hPdegree).trans_lt hdegree)

end ReedSolomon.HiddenDerivative
