/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/WeightedSupport.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 1 of the 19 declarations of the file is kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.FieldTheory.RatFunc.Basic
import ThirdParty.ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve
import ThirdParty.ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Basic

/-!
# Symbolic interpolation on weighted support and received curves

Every eligible exponent is represented by a source column, so the full weighted support can be
used as the column family of a symbolic interpolant. The local-coordinate matrix of each received
line or polynomial curve is a column submatrix of the canonical weighted-support matrix. Pointwise
rank bounds give a rank bound for the full matrix, and a dimension margin yields a primitive
interpolant with explicit challenge-degree and height bounds.

## Main statements

* `weightedSupportColumns`: a finite enumeration of the weighted-support exponents as source
  columns.
* `localConstraintBlock_eq_weightedSupportSubmatrix`,
  `localConstraintBlock_rank_le_base_actual` and
  `localConstraintMatrix_rank_le_weightedSupport`: block identification and rank bounds for
  arbitrary received polynomial curves.
* `exists_primitive_weightedSupport_interpolant`: primitive interpolation from a strict dimension
  surplus for arbitrary finite point and column types.
* `interpolant_mem_weightedSupportSpace`: assembled interpolants lie in the weighted-support space.
* `receivedLine_matrix_rank_le_base_actual`: the full symbolic matrix has rank at most the number
  of points times the actual local rank.
* `exists_symbolic_weightedSupport_interpolant_of_fixed_margin`: a dimension margin yields a
  primitive interpolant on the full support with degree and height bounds.
* `exists_constant_interpolant_of_zero_rank`: zero local rank yields a primitive interpolant with
  constant coefficients.

## References

* [DKT26]
* [DKTZ26]
-/

open PolynomialDifferential
open scoped BigOperators Polynomial Matrix

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {F : Type*} [Field F] {d D m W : ℕ} {L : ℝ}
variable {ι κ : Type*}

variable {R : Type*} [CommSemiring R] {κ : Type*} [Fintype κ]

/-- An interpolant of eligible source columns lies in the weighted-support space. -/
theorem interpolant_mem_weightedSupportSpace (hD : 0 < D) (columns : κ → SourceColumn d)
    (hband : ∀ j, WeightedSupportEligible D d W L (columns j).exponent) (v : κ → R) :
    SourceColumn.interpolant columns v ∈ weightedSupportSpace R D d W L hD := by
  rw [SourceColumn.interpolant]
  apply Submodule.sum_mem
  intro j _
  rw [mem_weightedSupportSpace_iff]
  intro u hu
  have heq : u = (columns j).exponent := by
    simpa using MvPolynomial.support_monomial_subset hu
  simpa only [heq] using hband j

end ReedSolomon.HiddenDerivative
