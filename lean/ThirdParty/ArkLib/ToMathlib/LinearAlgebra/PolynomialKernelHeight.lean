/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/ToMathlib/LinearAlgebra/PolynomialKernelHeight.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 1 of the 6 declarations of the file is kept. Kept are those that the proofs of
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
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.SimpleRing.Principal
import ThirdParty.ArkLib.ToMathlib.LinearAlgebra.Matrix.PrimitiveKernel
import ThirdParty.ArkLib.ToMathlib.Polynomial.DegreeLT

/-!
# Polynomial kernel vectors of uniformly bounded degree

For a polynomial matrix with `r` rows and `c` columns, suppose every entry has natural degree at
most `b` and `r < c`. This file constructs a nonzero vector in the right kernel whose coordinates
have degree strictly less than

`r * b / (c - r) + 1`.

The row count `r` may be replaced by any upper bound `s` on the rank of the matrix over a field
into which `F[X]` embeds, for example the rational function field, and the kernel vector may be
chosen primitive: its coordinates generate the unit ideal of `F[X]`.

## Main statements

* `Matrix.exists_ne_zero_mulVec_eq_zero_degreeLT` uses arbitrary finite row and column index
  types and records the bound as membership in `Polynomial.degreeLT`, including for zero
  coordinates. `Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le` is its natural-degree form.
* `Matrix.exists_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le` replaces the row count by an upper
  bound `s` on the rank of `M.map φ`, for any injective ring homomorphism `φ` from `F[X]` to a
  field. `Matrix.exists_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_le` is its natural-degree
  form.
* `Matrix.exists_primitive_kernel_vector_degreeLT`: dividing a nonzero polynomial kernel vector by
  the gcd of its coordinates gives a primitive kernel vector that keeps every coordinate in its
  own `degreeLT` budget.
* `Matrix.exists_primitive_ne_zero_mulVec_eq_zero_degreeLT_of_rank_le` adds to the rank form the
  conclusion that the coordinates of the kernel vector generate the unit ideal.
## Proof outline

The row-count theorem treats the bounded coefficients of the kernel vector as scalar unknowns.
Multiplication by the matrix followed by coefficient extraction is a linear map between
finite-dimensional spaces; the displayed bound makes its source dimension larger than its target
dimension, so rank-nullity supplies a nonzero vector in its kernel.

For the rank form, `Matrix.exists_rows_submatrix_mulVec_eq_zero_iff` selects `rank (M.map φ)`
rows of `M` with the same right kernel as `M`. The row-count theorem applies to this submatrix,
and the resulting bound is at most the bound for `s` because `r * b / (c - r)` is monotone in
`r` for `r < c`. For the primitive form, `Matrix.exists_primitive_kernel_vector_degreeLT` applies
`Matrix.exists_primitive_kernel_vector_eq_smul`, which writes the kernel vector as `g • u` with
`g ≠ 0` and `u` primitive, and `Polynomial.mem_degreeLT_of_mul_left` (in
`ArkLib.ToMathlib.Polynomial.DegreeLT`) transfers the degree bound from `g * u j` to `u j`.
The natural-degree forms follow from the `degreeLT` forms by
`Polynomial.natDegree_le_of_mem_degreeLT_succ`.

## References

* [DKT26]
-/

open Polynomial

namespace Matrix

variable {F : Type*} [Field F]

/-- Primitive normalization of a polynomial kernel vector preserves per-coordinate degree budgets.

Let `v ≠ 0` satisfy `M *ᵥ v = 0` and `v j ∈ Polynomial.degreeLT F (slots j)` for every `j`. Then
some `u ≠ 0` with `M *ᵥ u = 0` has `u j ∈ Polynomial.degreeLT F (slots j)` for every `j` and
`Ideal.span (Set.range u) = ⊤`. The vector `u` is `v` divided by the gcd of its coordinates, so
each `v j` is a nonzero multiple of `u j` and its degree bound passes to `u j`. The budgets may
differ between coordinates, and a budget `slots j = 0` (which forces `v j = 0`) also forces
`u j = 0`. The hypothesis `v ≠ 0` is needed because the zero vector has no primitive multiple.
The row index type is arbitrary. -/
theorem exists_primitive_kernel_vector_degreeLT {rows cols : Type*} [Fintype cols]
    (M : Matrix rows cols F[X]) (slots : cols → ℕ) {v : cols → F[X]} (hv : v ≠ 0)
    (hMv : M *ᵥ v = 0) (hvdegree : ∀ j, v j ∈ Polynomial.degreeLT F (slots j)) :
    ∃ u : cols → F[X],
      u ≠ 0 ∧ M *ᵥ u = 0 ∧ (∀ j, u j ∈ Polynomial.degreeLT F (slots j)) ∧
        Ideal.span (Set.range u) = ⊤ := by
  classical
  obtain ⟨g, u, hg, rfl, hu, hMu, hspan⟩ := M.exists_primitive_kernel_vector_eq_smul hv hMv
  exact ⟨u, hu, hMu, fun j ↦ Polynomial.mem_degreeLT_of_mul_left hg (hvdegree j), hspan⟩

end Matrix
