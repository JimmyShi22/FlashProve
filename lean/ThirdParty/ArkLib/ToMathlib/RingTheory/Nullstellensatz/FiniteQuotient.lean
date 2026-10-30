/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/ToMathlib/RingTheory/Nullstellensatz/FiniteQuotient.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 4 of the 5 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Point counts from finite coordinate quotients

A point of the zero locus of an ideal `I : Ideal (MvPolynomial σ k)` determines a
`k`-algebra homomorphism from the actual coordinate quotient `MvPolynomial σ k ⧸ I` to the
coordinate field. Distinct points determine distinct homomorphisms because their values on the
coordinate variables differ.

When the coordinate quotient is finite-dimensional, Mathlib's linear independence of algebra
homomorphisms supplies both finiteness of the homomorphism type and the sharp bound by the
quotient's `k`-dimension. Consequently the zero locus is finite and its `Set.ncard` is at most the
quotient's `k`-finrank.

Apart from the Krull-dimension-zero corollary, no finiteness hypothesis on `σ` is needed, and no
properness or radicality hypothesis on `I` or algebraic-closure hypothesis on the coordinate field
is needed anywhere. In particular the results include `I = ⊤`: both the
zero locus and the algebra-homomorphism type are empty, while the quotient has finrank zero.

## Main statements

* `MvPolynomial.zeroLocusPointHom`: evaluation of the coordinate quotient at a zero.
* `MvPolynomial.zeroLocusPointHom_injective`: distinct zeros induce distinct algebra homomorphisms.
* `MvPolynomial.finite_zeroLocus_of_finite_quotient`: a finite-dimensional coordinate quotient has
  finitely many points over every field extension.
* `MvPolynomial.ncard_zeroLocus_le_finrank_quotient`: the point count is bounded by the
  base-field dimension of the actual coordinate quotient.
* `MvPolynomial.finite_zeroLocus_and_ncard_le_of_krullDimLE_zero`: the same two conclusions for a
  coordinate quotient of Krull dimension zero in finitely many variables.

## Ownership

The generic algebra result is already owned by Mathlib:
`Finite.algHom` and `card_algHom_le_finrank` in
`Mathlib.LinearAlgebra.FreeModule.Finite.Matrix`. This module adds only the multivariate-polynomial
zero-locus adapter and does not duplicate that generic API. The passage from Krull dimension zero
to a finite-dimensional quotient is Mathlib's `Module.finite_iff_krullDimLE_zero` for finite-type
algebras over a field; it is the only place where finitely many variables are needed.
The Hilbert-polynomial form of the bound is in
`ArkLib.ToMathlib.RingTheory.Nullstellensatz.AffineHilbertPolynomial`.
-/

noncomputable section

namespace MvPolynomial

variable {k K σ : Type*} [Field k] [Field K] [Algebra k K]

/-- Evaluate the coordinate quotient at one of its zeros. -/
def zeroLocusPointHom (I : Ideal (MvPolynomial σ k)) (x : zeroLocus K I) :
    (MvPolynomial σ k ⧸ I) →ₐ[k] K :=
  Ideal.Quotient.liftₐ I (aeval x.val) x.property

/-- A point is determined by its homomorphism on the coordinate quotient. -/
theorem zeroLocusPointHom_injective (I : Ideal (MvPolynomial σ k)) :
    Function.Injective (zeroLocusPointHom (K := K) I) := by
  intro x y h
  apply Subtype.ext
  funext i
  have hi := DFunLike.congr_fun h (Ideal.Quotient.mk I (X i))
  change aeval x.val (X i) = aeval y.val (X i) at hi
  simpa only [aeval_X] using hi

/-- A finite-dimensional coordinate quotient has finitely many extension-field zeros. -/
theorem finite_zeroLocus_of_finite_quotient (I : Ideal (MvPolynomial σ k))
    [Module.Finite k (MvPolynomial σ k ⧸ I)] : (zeroLocus K I).Finite := by
  have : Finite (zeroLocus K I) := Finite.of_injective
    (zeroLocusPointHom I) (zeroLocusPointHom_injective I)
  exact Set.toFinite _

/-- The number of distinct zeros is at most the dimension of the actual coordinate quotient.

The finite-dimensional hypothesis already implies finiteness by
`finite_zeroLocus_of_finite_quotient`, so the left side is the genuine finite cardinality rather
than the default value of `Set.ncard` for an infinite set. -/
theorem ncard_zeroLocus_le_finrank_quotient (I : Ideal (MvPolynomial σ k))
    [Module.Finite k (MvPolynomial σ k ⧸ I)] :
    (zeroLocus K I).ncard ≤ Module.finrank k (MvPolynomial σ k ⧸ I) := by
  have h := Nat.card_le_card_of_injective (zeroLocusPointHom (K := K) I)
    (zeroLocusPointHom_injective I)
  exact h.trans (card_algHom_le_finrank k (MvPolynomial σ k ⧸ I) K)

end MvPolynomial

end
