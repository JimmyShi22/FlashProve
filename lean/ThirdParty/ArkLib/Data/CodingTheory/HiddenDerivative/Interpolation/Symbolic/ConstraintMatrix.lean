/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/ConstraintMatrix.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 7 of the 14 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import ThirdParty.ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ChallengeDegree

/-!
# The local constraint matrix of a family of source columns

Given received points `(centers i, received i)` indexed by `ι` and source columns indexed by `κ`,
`localConstraintMatrix m centers received columns` has one row for each point `i` and each local
exponent of contact order below `m`, and one column for each source column. Its entry is the
coefficient of that local exponent in the unscaled substitution of the column's monomial at the
point. A coefficient vector `v` is in its kernel exactly when the interpolant
`SourceColumn.interpolant columns v` satisfies the local constraints at every point.

The row type is infinite for `m > 0`, but only finitely many rows are nonzero.
`localConstraintSupportedRows` is the finite set of these rows, and
`supportedLocalConstraintMatrix` is the restriction to them. The restriction has the same kernel,
and after any ring homomorphism into a field the same rank.

Over a polynomial ring `F[X]` in a symbolic challenge, with constant centers and received values
of challenge degree at most `ℓ`, the column of a source column with `Y₀` exponent `y₀` has
challenge degree at most `ℓ * y₀`. A row whose local exponent has jet degree `t` has challenge
degree at most `ℓ * (y₀ + ∑_j higher j - t)` in that column, and is zero there when `t`
exceeds the column's total jet degree.

## Main statements

* `localConstraintMatrix_mulVec_eq_zero_iff`: the kernel is the set of coefficient vectors whose
  interpolant satisfies all the local constraints.
* `localConstraintMatrix_apply_eq_localConstraintAt_coeff`: a matrix entry is a coefficient of
  the projected local constraint.
* `mem_localConstraintSupportedRows_iff`: the supported rows are the rows with a nonzero entry.
* `supportedLocalConstraintMatrix_mulVec_eq_zero_iff` and
  `rank_map_supportedLocalConstraintMatrix`: the restriction to the supported rows keeps the
  kernel and the rank.
* `natDegree_localConstraintMatrix_le`, `natDegree_localConstraintMatrix_le_sub` and
  `localConstraintMatrix_eq_zero_of_lt`: the entry bounds over a polynomial ring.

## References

* [DKT26]
-/

open PolynomialDifferential
open scoped Polynomial Matrix

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R] {d : ℕ} {ι κ : Type*}

/-! ### The matrix and its kernel -/

/-- The local constraint matrix: the entry in row `(i, e)` and column `j` is the coefficient of
the low-contact exponent `e` in the unscaled substitution of `(columns j).polynomial` at
`(centers i, received i)`. -/
def localConstraintMatrix (m : ℕ) (centers received : ι → R)
    (columns : κ → SourceColumn d) :
    Matrix (ι × LowContactIndex d m) κ R := fun row j =>
  localConstraintCoordinatesAt m (centers row.1) (received row.1) (columns j).polynomial row.2

/-- An entry of the local constraint matrix is a coefficient of a substituted column. -/
@[simp]
theorem localConstraintMatrix_apply (m : ℕ) (centers received : ι → R)
    (columns : κ → SourceColumn d) (row : ι × LowContactIndex d m) (j : κ) :
    localConstraintMatrix m centers received columns row j =
      (unscaledLocalSubstitution d (centers row.1) (received row.1)
        (columns j).polynomial).coeff row.2.1 :=
  rfl

/-- At a low-contact row, a matrix entry is the corresponding coefficient of the local constraint
polynomial. -/
theorem localConstraintMatrix_apply_eq_localConstraintAt_coeff (m : ℕ)
    (centers received : ι → R)
    (columns : κ → SourceColumn d) (row : ι × LowContactIndex d m) (j : κ) :
    localConstraintMatrix m centers received columns row j =
      (localConstraintAt m (centers row.1) (received row.1) (columns j).polynomial).coeff
        row.2.1 := by
  simp only [localConstraintMatrix_apply, localConstraintAt, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply, coeff_projectLowContact]
  simp [row.2.2]

variable [Fintype κ]

/-- Row `(i, e)` of `M *ᵥ v` is the coordinate at `e` of the local constraints of the interpolant
at point `i`. -/
theorem localConstraintMatrix_mulVec_apply (m : ℕ) (centers received : ι → R)
    (columns : κ → SourceColumn d) (v : κ → R) (row : ι × LowContactIndex d m) :
    (localConstraintMatrix m centers received columns *ᵥ v) row =
      localConstraintCoordinatesAt m (centers row.1) (received row.1)
        (SourceColumn.interpolant columns v) row.2 := by
  simp only [Matrix.mulVec, dotProduct, SourceColumn.interpolant_eq_sum_smul, map_sum,
    map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- A coefficient vector is in the kernel of the local constraint matrix exactly when its
interpolant satisfies the local constraints at every point. -/
theorem localConstraintMatrix_mulVec_eq_zero_iff (m : ℕ) (centers received : ι → R)
    (columns : κ → SourceColumn d) (v : κ → R) :
    localConstraintMatrix m centers received columns *ᵥ v = 0 ↔
      ∀ i, SatisfiesLocalConstraints m (centers i) (received i)
        (SourceColumn.interpolant columns v) := by
  simp only [satisfiesLocalConstraints_iff_coordinates_eq_zero, funext_iff, Pi.zero_apply,
    localConstraintMatrix_mulVec_apply, Prod.forall]

/-! ### Supported rows -/

variable [Fintype ι]

end ReedSolomon.HiddenDerivative

/-! ### Entry bounds over a polynomial ring -/

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R] {d : ℕ} {ι κ : Type*}

/-- With constant centers and received values of challenge degree at most `ℓ`, the entry in a
row whose local exponent has jet degree `t` and a column of total jet degree `y₀ + ∑_j higher j`
has challenge degree at most `ℓ * (y₀ + ∑_j higher j - t)`. -/
theorem natDegree_localConstraintMatrix_le_sub (m ℓ : ℕ) (centers : ι → R)
    (received : ι → R[X]) (hreceived : ∀ i, (received i).natDegree ≤ ℓ)
    (columns : κ → SourceColumn d) (row : ι × LowContactIndex d m) (j : κ) :
    (localConstraintMatrix m (Polynomial.C ∘ centers) received columns row j).natDegree ≤
      ℓ * ((columns j).y₀ + ∑ k, (columns j).higher k -
        row.2.1.weight (localJetDegreeWeight d)) :=
  SourceColumn.natDegree_coeff_unscaledLocalSubstitution_le_sub ℓ _ (hreceived row.1) _ _

/-- An entry vanishes when the jet degree of its row exceeds the total jet degree of its column.
This holds for all centers and received values. -/
theorem localConstraintMatrix_eq_zero_of_lt (m : ℕ) (centers received : ι → R)
    (columns : κ → SourceColumn d) (row : ι × LowContactIndex d m) (j : κ)
    (hlt : (columns j).y₀ + ∑ k, (columns j).higher k <
      row.2.1.weight (localJetDegreeWeight d)) :
    localConstraintMatrix m centers received columns row j = 0 :=
  SourceColumn.coeff_unscaledLocalSubstitution_eq_zero_of_lt _ _ _ hlt

end ReedSolomon.HiddenDerivative
