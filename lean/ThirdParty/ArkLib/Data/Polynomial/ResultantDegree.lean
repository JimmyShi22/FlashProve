/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph, Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/Polynomial/ResultantDegree.lean, commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13.
Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 3 of the 11 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
* ArkLib's file imports the package CompPoly for Polynomial.Bivariate.degreeX and
  Polynomial.Bivariate.coeff_natDegree_le_degreeX. Here the two names come from
  ThirdParty/ArkLibShim/BivariateDegreeX.lean, which was written for this library.
-/

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import ThirdParty.ArkLibShim.BivariateDegreeX

/-!
# Coefficient-variable degree bounds for resultants

The Sylvester matrix has one column budget per shifted input polynomial. Summing those budgets
bounds the degree of every determinant term. Adapted from Alexander Hicks and Aleph's
field-only result in ArkLib (Apache-2.0), generalizing the
`ps_nat_degree_resultant_le` argument to commutative coefficient rings and explicit coefficient
budgets, including padded resultants. For `R = F[Z]`, the resulting bound is in the middle `X`
axis of `F[Z][X][Y]`.

Source and adaptation: the native ArkLib theorem is at
https://github.com/Verified-zkEVM/ArkLib/blob/66f3d089a41704597f54d641b78254d2a8f361f8/ArkLib/Data/CodingTheory/PolishchukSpielman/Resultant.lean#L43-L98
The explicit coefficient budgets and derivative corollaries below extend that argument.
No donor compatibility modules are imported.

## Total-degree bounds

Suppose `P, Q : R[X][X]` have declared outer degrees `m`, `n` and satisfy the coefficient
triangles `i + deg_X (P.coeff i) ≤ dP` for `i ≤ m` and `i + deg_X (Q.coeff i) ≤ dQ` for `i ≤ n`;
for `m` and `n` the actual outer degrees, these say that `P` and `Q` have total degree at most
`dP` and `dQ`. Then `deg_X (resultant P Q m n) + m * n ≤ n * dP + m * dQ`. The proof bounds each
nonzero Sylvester determinant term by column weights and uses that a permutation preserves the
sum of the row indices. For the derivative, `dQ = dP - 1`, which gives the bound
`(2 * b - 1) * j - b ^ 2` of the source.

## Main statements

* `natDegree_resultant_le_of_coeff_natDegree_le`: the column-budget bound `n * A + m * B`.
* `Bivariate.degreeX_derivative_le`: differentiation in the outer variable does not increase
  `degreeX`.
* `natDegree_resultant_derivative_le` and `natDegree_resultant_derivative_padded_le`: the
  `(2 * d - 1) * degreeX P` bound for the derivative resultant.
* `natDegree_resultant_add_mul_le_of_coeff_add_le` and
  `natDegree_resultant_le_of_coeff_add_le`: the total-degree bound
  `n * dP + m * dQ - m * n`.
* `natDegree_resultant_le_mul_of_coeff_add_le`: the Bezout bound `dP * dQ`.
* `natDegree_resultant_derivative_padded_add_sq_le` and
  `natDegree_resultant_derivative_padded_le_of_coeff_add_le`: the derivative case
  `deg_X (resultant A A.derivative b (b - 1)) ≤ (2 * b - 1) * j - b ^ 2`.

The total-degree bounds are ported from ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/ToMathlib/Polynomial/DerivativeResultantDegree.lean`:
`natDegree_separableResultant_add_sq_le_of_le`, `natDegree_separableResultant_add_sq_le`,
`natDegree_separableResultant_le_totalDegree_of_le` and
`natDegree_separableResultant_le_totalDegree`. The source proves only the derivative case, for
`separableResultant A b = resultant A.derivative A (b - 1) b`, and assumes `0 < b` and
`A.natDegree = b`. Here the proof is done once for two arbitrary polynomials with declared
degrees, and the derivative case is a corollary stated in main's argument order
`resultant A A.derivative b (b - 1)`, which has the same value
(`resultant_comm_sub_one` in `ArkLib.Data.Polynomial.ResultantSpecialization`). Neither `0 < b`
nor `A.natDegree = b` is needed: only coefficients of index at most `b` enter the Sylvester
matrix, and for `b = 0` both sides are `0`. The source's forms with the triangle at every index
are the special case of the `i ≤ b` forms and are not restated.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S.,
  *On Proximity Gaps for Reed--Solomon Codes*][BCHKS25], Section 3.2.
-/

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- A padded resultant's coefficient-variable degree is bounded by the Sylvester column count
times each input's coefficient-degree budget. No degree or nonzero assumptions are necessary. -/
theorem natDegree_resultant_le_of_coeff_natDegree_le
    (P Q : Polynomial (Polynomial R)) (m n A B : ℕ)
    (hP : ∀ j, (P.coeff j).natDegree ≤ A) (hQ : ∀ j, (Q.coeff j).natDegree ≤ B) :
    (resultant P Q m n).natDegree ≤ n * A + m * B := by
  classical
  let M := sylvester P Q m n
  let cb : Fin (m + n) → ℕ :=
    Fin.addCases (fun _ : Fin m ↦ B) (fun _ : Fin n ↦ A)
  have hentry (σ : Equiv.Perm (Fin (m + n))) (i : Fin (m + n)) :
      (M (σ i) i).natDegree ≤ cb i := by
    cases i using Fin.addCases with
    | left j =>
      simp only [cb, Fin.addCases_left]
      have hM : M (σ (.castAdd n j)) (.castAdd n j) =
          if (σ (.castAdd n j) : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + n) then
            Q.coeff ((σ (.castAdd n j) : ℕ) - j) else 0 := by
        simp [M, sylvester]
      rw [hM]
      split_ifs
      · exact hQ _
      · simp
    | right j =>
      simp only [cb, Fin.addCases_right]
      have hM : M (σ (.natAdd m j)) (.natAdd m j) =
          if (σ (.natAdd m j) : ℕ) ∈ Set.Icc (j : ℕ) ((j : ℕ) + m) then
            P.coeff ((σ (.natAdd m j) : ℕ) - j) else 0 := by
        simp [M, sylvester]
      rw [hM]
      split_ifs
      · exact hP _
      · simp
  change M.det.natDegree ≤ _
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  refine (natDegree_smul_le _ _).trans ?_
  refine (natDegree_prod_le Finset.univ (fun i ↦ M (σ i) i)).trans ?_
  refine (Finset.sum_le_sum (fun i _ ↦ hentry σ i)).trans ?_
  simp [cb, Fin.sum_univ_add, Nat.add_comm]

/-- Differentiating in the outer variable does not increase any coefficient-variable degree. -/
theorem coeff_derivative_natDegree_le (P : Polynomial (Polynomial R)) (j : ℕ) :
    (P.derivative.coeff j).natDegree ≤ (P.coeff (j + 1)).natDegree := by
  rw [coeff_derivative]
  rw [show (j : Polynomial R) + 1 = C ((j : R) + 1) by simp]
  exact natDegree_mul_C_le _ _

/-- Padding the derivative to degree `d - 1` obeys the same coefficient-variable bound.
The derivative may have smaller actual degree, including in positive characteristic. -/
theorem natDegree_resultant_derivative_padded_le (P : Polynomial (Polynomial R)) :
    (resultant P P.derivative P.natDegree (P.natDegree - 1)).natDegree ≤
      (2 * P.natDegree - 1) * Bivariate.degreeX P := by
  have h := natDegree_resultant_le_of_coeff_natDegree_le P P.derivative
    P.natDegree (P.natDegree - 1) (Bivariate.degreeX P) (Bivariate.degreeX P)
    (Bivariate.coeff_natDegree_le_degreeX P)
    (fun j ↦ (coeff_derivative_natDegree_le P j).trans
      (Bivariate.coeff_natDegree_le_degreeX P (j + 1)))
  have hn : P.natDegree - 1 + P.natDegree = 2 * P.natDegree - 1 := by omega
  simpa only [← add_mul, hn] using h

/-! ### Total-degree bounds -/

end Polynomial
