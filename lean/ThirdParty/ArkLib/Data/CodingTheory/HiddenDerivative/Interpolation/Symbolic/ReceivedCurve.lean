/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/ReceivedCurve.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 2 of the 4 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import Mathlib.Algebra.Order.Ring.Star
import ThirdParty.ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.ConstraintMatrix
import ThirdParty.ArkLib.ToMathlib.LinearAlgebra.PolynomialKernelHeight

/-!
# Symbolic interpolation for received polynomial curves

The received value at each point is a polynomial `received i` of degree at most `ℓ` in a symbolic
challenge, and the centers are constants. A rank bound `s` for the local constraint matrix, after
an injective ring homomorphism from `F[X]` into a field, with `s` below the number of source
columns, gives a coefficient vector `v` over `F[X]` such that the interpolant
`SourceColumn.interpolant columns v`

* satisfies the local constraints at every point, as polynomials in the challenge;
* has coefficients of challenge degree at most `s * (ℓ * ν) / (card κ - s)`, where `ν` bounds the
  `Y₀` exponents of the columns;
* has coefficients that generate the unit ideal of `F[X]`, so its image under every ring
  homomorphism from `F[X]` into a nontrivial semiring is nonzero. In particular it stays nonzero
  after every specialization of the challenge, in `F` or in an extension field.

The rank bound is a hypothesis. The received line `f + Z g` is the case `ℓ = 1`.

## Main statements

* `exists_primitive_interpolant_of_rank_le`: the construction for received curves.
* `exists_primitive_receivedLine_interpolant_of_rank_le`: the case of received lines.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26]
-/

open PolynomialDifferential
open scoped Polynomial Matrix

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {F : Type*} [Field F] {d : ℕ} {ι κ : Type*} [Finite ι] [Fintype κ]

/-- The received value `f + Z g` of a line, as a polynomial in the challenge `Z`. -/
def receivedLine (f g : F) : F[X] :=
  Polynomial.C f + Polynomial.X * Polynomial.C g

/-- A received line has challenge degree at most `1`. -/
theorem natDegree_receivedLine_le (f g : F) : (receivedLine f g).natDegree ≤ 1 := by
  rw [receivedLine]
  compute_degree

end ReedSolomon.HiddenDerivative
