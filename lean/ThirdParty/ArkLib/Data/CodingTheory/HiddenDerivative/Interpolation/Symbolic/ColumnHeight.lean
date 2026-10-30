/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/ColumnHeight.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 1 of the 3 declarations of the file is kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ReceivedCurve
import ThirdParty.ArkLib.ToMathlib.LinearAlgebra.ShiftedPolynomialKernelHeight

/-!
# Symbolic interpolation with column-dependent challenge degrees

With constant centers and received values of challenge degree at most `ℓ`, the column of a source
column with `Y₀` exponent `y₀` has challenge degree at most `ℓ * y₀`
(`natDegree_localConstraintMatrix_le`). At a target height `h`, that column can therefore carry a
coefficient of challenge degree below `h + 1 - ℓ * y₀`, which is none when `ℓ * y₀ > h`. If a rank
bound `s` for the local constraint matrix satisfies

```text
s * (h + 1) < ∑_j (h + 1 - ℓ * y₀(j)),
```

then there is a primitive interpolant whose coefficient in column `j` has degree below
`h + 1 - ℓ * y₀(j)`, in particular at most `h`. It satisfies the local constraints at every point
and stays nonzero under every ring homomorphism from `F[X]` into a nontrivial semiring.

## Main statements

* `exists_primitive_interpolant_of_column_height`: the construction for received curves.
* `exists_primitive_receivedLine_interpolant_of_column_height`: the case of received lines.
* `exists_primitive_interpolant_of_shifted_height`: the construction from shifted row and
  column weights.

## References

* [DKT26]
-/

open PolynomialDifferential
open scoped Polynomial Matrix

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {F : Type*} [Field F] {d : ℕ} {ι κ : Type*} [Finite ι] [Fintype κ]

/-- A strict surplus of shifted row and column slots, with a matrix kernel implying the local
constraints, yields a primitive curve interpolant whose coefficient in column `j` has degree
below `h + 1 - ℓ * totalJetDegree (columns j).exponent`. -/
theorem exists_primitive_interpolant_of_shifted_height {n N rows : ℕ}
    (m ℓ h : ℕ) (centers : Fin n → F) (w : Fin n → F[X])
    (columns : Fin N → SourceColumn d) (hcolumns : Function.Injective columns)
    (M : Matrix (Fin rows) (Fin N) F[X]) (rowWeight : Fin rows → ℕ)
    (hkernel : ∀ v, M *ᵥ v = 0 →
      ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i))
        (w i) (SourceColumn.interpolant columns v))
    (hdegree : ∀ i j, rowWeight i ≤ ℓ * totalJetDegree (columns j).exponent →
      (M i j).natDegree ≤ ℓ * totalJetDegree (columns j).exponent - rowWeight i)
    (hzero : ∀ i j, ℓ * totalJetDegree (columns j).exponent < rowWeight i → M i j = 0)
    (hsurplus : Finset.univ.sum (fun i : Fin rows ↦ h + 1 - rowWeight i) <
      Finset.univ.sum (fun j : Fin N ↦
        h + 1 - ℓ * totalJetDegree (columns j).exponent)) :
    ∃ v : Fin N → F[X], v ≠ 0 ∧
      (∀ j, v j ∈ Polynomial.degreeLT F
        (h + 1 - ℓ * totalJetDegree (columns j).exponent)) ∧
      Ideal.span (Set.range v) = ⊤ ∧
      (∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
        MvPolynomial.map (Polynomial.eval₂RingHom ι z)
          (SourceColumn.interpolant columns v) ≠ 0) ∧
      ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i))
        (w i) (SourceColumn.interpolant columns v) := by
  obtain ⟨v, hv, hMv, hvdegree, hprimitive⟩ :=
    Matrix.exists_primitive_ne_zero_mulVec_eq_zero_shifted_degreeLT_of_natDegree_le
      M rowWeight (fun j ↦ ℓ * totalJetDegree (columns j).exponent) h hdegree hzero hsurplus
  refine ⟨v, hv, hvdegree, hprimitive, ?_, hkernel v hMv⟩
  intro E _ ι z
  exact SourceColumn.map_interpolant_ne_zero hcolumns (Polynomial.eval₂RingHom ι z)
    (Ideal.comp_ne_zero_of_span_range_eq_top hprimitive (Polynomial.eval₂RingHom ι z))

end ReedSolomon.HiddenDerivative
