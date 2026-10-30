/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/ToMathlib/LinearAlgebra/ShiftedPolynomialKernelHeight.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 4 of the 8 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import ThirdParty.ArkLib.ToMathlib.LinearAlgebra.PolynomialKernelHeight

/-!
# Polynomial kernel vectors with shifted row and column degree budgets

Let `M` be a matrix over `F[X]` whose columns carry weights `columnWeight j` and whose rows carry
weights `rowWeight i`, and suppose the entry `M i j` has degree less than
`columnWeight j + 1 - rowWeight i` (natural subtraction). Such matrices arise from graded maps:
the entry from source column `j` to target row `i` has degree at most the weight difference, and
it is zero when the difference is negative. At a height `h`, a kernel vector whose coordinate `j`
has degree less than `h + 1 - columnWeight j` produces row `i` of degree less than
`h + 1 - rowWeight i`. Counting coefficients, the columns supply
`∑ j, (h + 1 - columnWeight j)` unknowns and the rows impose `∑ i, (h + 1 - rowWeight i)`
equations. This file shows that a strict surplus of unknowns gives a nonzero kernel vector with
these coordinate budgets, and that the vector can be chosen primitive.

The case of zero row weights is the column form: every entry of column `j` has natural degree at
most `weight j`, and the surplus reads `card rows * (h + 1) < ∑ j, (h + 1 - weight j)`. It
retains the individual column degrees that the uniform theorem
`Matrix.exists_ne_zero_mulVec_eq_zero_degreeLT` replaces by their maximum. In the column form the
row count may be replaced by an upper bound on the rank.

## Main statements

* `Polynomial.mem_degreeLT_add_one_sub_iff`: membership in `degreeLT R (c + 1 - r)` is the pair of
  conditions "natural degree at most `c - r` when `r ≤ c`" and "zero when `c < r`".
* `Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT`: the shifted kernel theorem, over
  arbitrary finite index types, with the entry hypothesis
  `∀ i j, columnWeight j ≤ h → M i j ∈ degreeLT F (columnWeight j + 1 - rowWeight i)`.
  `Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT_of_natDegree_le` takes instead the two
  hypotheses `hdegree` (natural degree at most the weight difference when it is nonnegative) and
  `hzero` (zero when it is negative).
* `Matrix.exists_primitive_ne_zero_mulVec_eq_zero_shifted_degreeLT` and its form
  `Matrix.exists_primitive_ne_zero_mulVec_eq_zero_shifted_degreeLT_of_natDegree_le` with `hdegree`
  and `hzero` add the conclusion `Ideal.span (Set.range v) = ⊤` and keep every coordinate budget.
* `Matrix.exists_ne_zero_mulVec_eq_zero_column_degreeLT`: the column form with the row count.
* `Matrix.exists_ne_zero_mulVec_eq_zero_column_degreeLT_of_rank_le`: the column form with an
  upper bound `s` on the rank of `M.map φ` for an injective `φ : F[X] →+* K` into a field, and
  `Matrix.exists_primitive_ne_zero_mulVec_eq_zero_column_degreeLT_of_rank_le`, its primitive form.

## Proof outline

The shifted theorem treats the coefficients of the coordinates as scalar unknowns: coordinate `j`
is decoded from `h + 1 - columnWeight j` coefficients. The linear map that multiplies by `M` and
keeps the first `h + 1 - rowWeight i` coefficients of row `i` has source dimension larger than
target dimension, so rank-nullity gives a nonzero vector in its kernel. The entry hypothesis
makes every product `M i j * v j` lie in `degreeLT F (h + 1 - rowWeight i)`, so the coefficients
that were not extracted vanish as well, and the decoded vector is a polynomial kernel vector.

The column form is the case `rowWeight = 0`. The rank form applies it to the rank-many rows
selected by `Matrix.exists_rows_submatrix_mulVec_eq_zero_iff`. The primitive forms apply
`Matrix.exists_primitive_kernel_vector_degreeLT`, which divides by the gcd of the coordinates and
keeps each coordinate in its `degreeLT` budget.

## The entry hypothesis

The entry hypothesis is required only for columns with `columnWeight j ≤ h`. A column with
`columnWeight j > h` has zero coefficient slots, its coordinate is forced to be `0`, and its
entries never enter `M *ᵥ v`. For the remaining columns the condition is also necessary for the
coefficient count to be valid entrywise: `M i j * p` lies in `degreeLT F (h + 1 - rowWeight i)`
for every `p ∈ degreeLT F (h + 1 - columnWeight j)` exactly when
`M i j ∈ degreeLT F (columnWeight j + 1 - rowWeight i)`, as the choice
`p = X ^ (h - columnWeight j)` shows.
When `columnWeight j < rowWeight i` the budget is `degreeLT F 0 = ⊥`, so the hypothesis says
`M i j = 0`. Stating it with `degreeLT` rather than with `natDegree` avoids treating a nonzero
constant in such a position as admissible.

## Rank forms of the shifted theorem

A shifted analogue of the rank form is omitted. Replacing `M` by a set of rows with the same
kernel changes the row-slot sum `∑ i, (h + 1 - rowWeight i)` according to which rows are chosen,
and a row basis is not canonical, so the rank alone does not determine the bound. The only
selection-independent estimate uses a lower bound `w ≤ rowWeight i` for all rows; but then the
entry hypothesis can be weakened to the constant row weight `w`, and the statement is the column
form after shifting all weights by `w` (columns of weight below `w` are zero columns). A caller
that knows a good set of rows can apply `Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT`
to `M.submatrix rows id` and transport the kernel with
`Matrix.exists_rows_submatrix_mulVec_eq_zero_iff` or its own kernel equivalence.
-/

open Polynomial

namespace Polynomial

/-- Membership in the shifted budget `degreeLT R (c + 1 - r)` is equivalent to the pair of
conditions: natural degree at most `c - r` when `r ≤ c`, and the zero
polynomial when `c < r`.

Subtraction is natural subtraction, so the budget is `0` exactly when `c < r`, and
`degreeLT R 0 = ⊥`. When `r ≤ c` the budget is `(c - r) + 1`, and membership is the natural-degree
bound `natDegree ≤ c - r`, which holds for the zero polynomial as well. -/
theorem mem_degreeLT_add_one_sub_iff {R : Type*} [Semiring R] {p : R[X]} {c r : ℕ} :
    p ∈ degreeLT R (c + 1 - r) ↔ (r ≤ c → p.natDegree ≤ c - r) ∧ (c < r → p = 0) := by
  by_cases hrc : r ≤ c
  · rw [show c + 1 - r = (c - r) + 1 by omega, degreeLT_succ_eq_degreeLE, mem_degreeLE,
      ← natDegree_le_iff_degree_le]
    exact ⟨fun hp ↦ ⟨fun _ ↦ hp, fun hcr ↦ absurd hcr (Nat.not_lt.mpr hrc)⟩,
      fun hp ↦ hp.1 hrc⟩
  · rw [show c + 1 - r = 0 by omega, degreeLT_zero, Submodule.mem_bot]
    exact ⟨fun hp ↦ ⟨fun hrc' ↦ absurd hrc' hrc, fun _ ↦ hp⟩,
      fun hp ↦ hp.2 (Nat.lt_of_not_ge hrc)⟩

end Polynomial

namespace Matrix

variable {F : Type*} [Field F]

/-- A strict surplus of shifted coefficient slots gives a nonzero polynomial kernel vector.

Let column `j` have weight `columnWeight j` and row `i` weight `rowWeight i`. Suppose every entry
of a column of weight at most `h` satisfies
`M i j ∈ degreeLT F (columnWeight j + 1 - rowWeight i)`, and that
`∑ i, (h + 1 - rowWeight i) < ∑ j, (h + 1 - columnWeight j)`. Then there is `v ≠ 0` with
`M *ᵥ v = 0` and `v j ∈ degreeLT F (h + 1 - columnWeight j)` for every `j`.

All subtractions are natural subtraction. The entry hypothesis is what makes each product
`M i j * v j` fit into the `h + 1 - rowWeight i` coefficients extracted from row `i`; when
`columnWeight j < rowWeight i` it says `M i j = 0`. The module docstring explains why this entry
condition is also necessary entrywise. The surplus is strict because a square system can have
only the zero solution.

Edge cases: a column with `columnWeight j > h` contributes no slots, its coordinate is `0`, and
its entries are unconstrained. A row with `rowWeight i > h` contributes no equations; the entry
hypothesis forces its entries in active columns to vanish, so it is annihilated by every vector
supported on active columns. The row type may be empty, in which case the surplus asks only for
one active column. If `h` is below every column weight, the right side of the surplus is `0` and
the hypothesis cannot hold. -/
theorem exists_ne_zero_mulVec_eq_zero_shifted_degreeLT {rows cols : Type*}
    [Fintype rows] [Fintype cols] (M : Matrix rows cols F[X]) (rowWeight : rows → ℕ)
    (columnWeight : cols → ℕ) (h : ℕ)
    (hentry : ∀ i j, columnWeight j ≤ h →
      M i j ∈ degreeLT F (columnWeight j + 1 - rowWeight i))
    (hsurplus : ∑ i, (h + 1 - rowWeight i) < ∑ j, (h + 1 - columnWeight j)) :
    ∃ v : cols → F[X], v ≠ 0 ∧ M *ᵥ v = 0 ∧
      ∀ j, v j ∈ degreeLT F (h + 1 - columnWeight j) := by
  classical
  let columnSlots := fun j ↦ h + 1 - columnWeight j
  let rowSlots := fun i ↦ h + 1 - rowWeight i
  let decode (j : cols) : (Fin (columnSlots j) → F) →ₗ[F] F[X] :=
    (degreeLT F (columnSlots j)).subtype ∘ₗ (degreeLTEquiv F (columnSlots j)).symm.toLinearMap
  let decodeVec : (∀ j, Fin (columnSlots j) → F) →ₗ[F] (cols → F[X]) :=
    LinearMap.pi fun j ↦ decode j ∘ₗ LinearMap.proj j
  let takeCoeffs : (rows → F[X]) →ₗ[F] (∀ i, Fin (rowSlots i) → F) :=
    LinearMap.pi fun i ↦ LinearMap.pi fun k ↦ lcoeff F k ∘ₗ LinearMap.proj i
  let coefficientMap : (∀ j, Fin (columnSlots j) → F) →ₗ[F] (∀ i, Fin (rowSlots i) → F) :=
    takeCoeffs ∘ₗ (M.mulVecLin.restrictScalars F) ∘ₗ decodeVec
  have hdim : Module.finrank F (∀ i, Fin (rowSlots i) → F) <
      Module.finrank F (∀ j, Fin (columnSlots j) → F) := by
    simpa [Module.finrank_pi_fintype, rowSlots, columnSlots] using hsurplus
  obtain ⟨c, hc, hcne⟩ := (LinearMap.ker coefficientMap).ne_bot_iff.mp
    (coefficientMap.ker_ne_bot_of_finrank_lt hdim)
  let v : cols → F[X] := fun j ↦ decode j (c j)
  have hvdegree (j : cols) : v j ∈ degreeLT F (columnSlots j) :=
    ((degreeLTEquiv F (columnSlots j)).symm (c j)).property
  have hproduct (i : rows) (j : cols) : M i j * v j ∈ degreeLT F (rowSlots i) := by
    by_cases hj : columnWeight j ≤ h
    · obtain ⟨hdeg, hzero⟩ := mem_degreeLT_add_one_sub_iff.mp (hentry i j hj)
      by_cases hij : rowWeight i ≤ columnWeight j
      · have hv : (v j).natDegree ≤ h - columnWeight j := by
          apply natDegree_le_of_mem_degreeLT_succ
          simpa [columnSlots, show h + 1 - columnWeight j = h - columnWeight j + 1 by omega]
            using hvdegree j
        rw [show rowSlots i = h - rowWeight i + 1 by simp only [rowSlots]; omega,
          degreeLT_succ_eq_degreeLE, mem_degreeLE, ← natDegree_le_iff_degree_le]
        exact (natDegree_mul_le_of_le (hdeg hij) hv).trans (by omega)
      · simp [hzero (Nat.lt_of_not_ge hij)]
    · have hslots : columnSlots j = 0 := by simp only [columnSlots]; omega
      have hv : v j = 0 := by
        simpa [hslots, degreeLT_zero] using hvdegree j
      simp [hv]
  have hmulVec : M *ᵥ v = 0 := by
    funext i
    have hrow : (M *ᵥ v) i ∈ degreeLT F (rowSlots i) :=
      Submodule.sum_mem _ fun j _ ↦ hproduct i j
    apply Polynomial.ext
    intro k
    by_cases hk : k < rowSlots i
    · have hcoefficient :=
        congrFun (congrFun (LinearMap.mem_ker.mp hc) i) (⟨k, hk⟩ : Fin (rowSlots i))
      have hdecodeVec : decodeVec c = v := by ext j; rfl
      simp only [coefficientMap, LinearMap.comp_apply] at hcoefficient
      rw [hdecodeVec] at hcoefficient
      simpa [takeCoeffs] using hcoefficient
    · simp only [Pi.zero_apply, coeff_zero]
      exact (degree_lt_iff_coeff_zero _ _).mp (mem_degreeLT.mp hrow) k (Nat.le_of_not_gt hk)
  have hvne : v ≠ 0 := by
    intro hv
    apply hcne
    have hdecode (j : cols) : Function.Injective (decode j) := by
      intro x y hxy
      exact (degreeLTEquiv F (columnSlots j)).symm.injective (Subtype.ext hxy)
    funext j
    exact hdecode j (by simpa [v] using congrFun hv j)
  exact ⟨v, hvne, hmulVec, hvdegree⟩

/-- A strict surplus of shifted coefficient slots gives a primitive polynomial kernel vector.

Under the hypotheses of `Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT`, the kernel
vector can also be chosen with `Ideal.span (Set.range v) = ⊤`, while every coordinate stays in
its own budget `degreeLT F (h + 1 - columnWeight j)`; in particular columns of weight above `h`
still have zero coordinates. Nonvanishing after specializing `X` in any field extension follows
from the unit-ideal conclusion by `Ideal.comp_ne_zero_of_span_range_eq_top`. -/
theorem exists_primitive_ne_zero_mulVec_eq_zero_shifted_degreeLT {rows cols : Type*}
    [Fintype rows] [Fintype cols] (M : Matrix rows cols F[X]) (rowWeight : rows → ℕ)
    (columnWeight : cols → ℕ) (h : ℕ)
    (hentry : ∀ i j, columnWeight j ≤ h →
      M i j ∈ degreeLT F (columnWeight j + 1 - rowWeight i))
    (hsurplus : ∑ i, (h + 1 - rowWeight i) < ∑ j, (h + 1 - columnWeight j)) :
    ∃ v : cols → F[X], v ≠ 0 ∧ M *ᵥ v = 0 ∧
      (∀ j, v j ∈ degreeLT F (h + 1 - columnWeight j)) ∧ Ideal.span (Set.range v) = ⊤ := by
  obtain ⟨v, hv, hMv, hvdegree⟩ :=
    exists_ne_zero_mulVec_eq_zero_shifted_degreeLT M rowWeight columnWeight h hentry hsurplus
  exact exists_primitive_kernel_vector_degreeLT M _ hv hMv hvdegree

/-- `Matrix.exists_primitive_ne_zero_mulVec_eq_zero_shifted_degreeLT` with the entry hypothesis
split into `hdegree` and `hzero` as in
`Matrix.exists_ne_zero_mulVec_eq_zero_shifted_degreeLT_of_natDegree_le`. The unit-ideal
conclusion implies `∀ {E} [Field E] (ι : F →+* E) (z : E), (fun j ↦ (v j).eval₂ ι z) ≠ 0`, by
`Ideal.comp_ne_zero_of_span_range_eq_top` applied to `Polynomial.eval₂RingHom ι z`. -/
theorem exists_primitive_ne_zero_mulVec_eq_zero_shifted_degreeLT_of_natDegree_le
    {rows cols : Type*} [Fintype rows] [Fintype cols] (M : Matrix rows cols F[X])
    (rowWeight : rows → ℕ) (columnWeight : cols → ℕ) (h : ℕ)
    (hdegree : ∀ i j, rowWeight i ≤ columnWeight j →
      (M i j).natDegree ≤ columnWeight j - rowWeight i)
    (hzero : ∀ i j, columnWeight j < rowWeight i → M i j = 0)
    (hsurplus : ∑ i, (h + 1 - rowWeight i) < ∑ j, (h + 1 - columnWeight j)) :
    ∃ v : cols → F[X], v ≠ 0 ∧ M *ᵥ v = 0 ∧
      (∀ j, v j ∈ degreeLT F (h + 1 - columnWeight j)) ∧ Ideal.span (Set.range v) = ⊤ :=
  exists_primitive_ne_zero_mulVec_eq_zero_shifted_degreeLT M rowWeight columnWeight h
    (fun i j _ ↦ mem_degreeLT_add_one_sub_iff.mpr ⟨hdegree i j, hzero i j⟩) hsurplus

end Matrix
