/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/ToMathlib/RingTheory/Nullstellensatz/AffineHilbertPolynomial.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 3 of the 4 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineDegree
import ThirdParty.ArkLib.ToMathlib.RingTheory.Nullstellensatz.FiniteQuotient

/-!
# Zero-dimensional point counts and the affine Hilbert polynomial

Let `k` be a field, `σ` a finite type and `I` an ideal of `MvPolynomial σ k` whose quotient is
finite-dimensional over `k`. Over every field extension `K` of `k`, the zero locus of `I` has at
most `(affineHilbertPolynomial I).coeff 0` points. The affine Hilbert polynomial of such an ideal
is the constant `Module.finrank k (MvPolynomial σ k ⧸ I)`
(`MvPolynomial.affineHilbertPolynomial_eq_C_finrank`), so the statement is
`MvPolynomial.ncard_zeroLocus_le_finrank_quotient` read through the Hilbert polynomial. The
finite-dimensional hypothesis is equivalent to Krull dimension zero of the quotient and to the
Hilbert polynomial having natural degree zero (`natDegree_affineHilbertPolynomial_eq_zero_iff`).
In that case the constant is also the affine degree `MvPolynomial.affineDegree I`, so the same
bound reads `ncard ≤ affineDegree I`.

## Main statements

* `MvPolynomial.ncard_zeroLocus_le_coeff_zero_affineHilbertPolynomial`: the bound for a
  finite-dimensional quotient.
* `MvPolynomial.finite_zeroLocus_and_ncard_le_affineHilbertPolynomial`: finiteness and the bound
  for a quotient of Krull dimension zero.
* `MvPolynomial.ncard_zeroLocus_le_affineDegree`,
  `MvPolynomial.finite_zeroLocus_and_ncard_le_affineDegree`: the same bound by the affine degree,
  for a finite-dimensional quotient and for a Hilbert polynomial of natural degree zero.
-/

noncomputable section

namespace MvPolynomial

variable {k K σ : Type*} [Field k] [Field K] [Algebra k K] [Finite σ]

/-- For a finite-dimensional coordinate quotient, the zero locus of `I` over any field extension
`K` has at most `(affineHilbertPolynomial I).coeff 0` points.

The finite-dimensional hypothesis is needed: over `k = K = ZMod 2` in one variable, the zero
ideal has a zero locus of two points, while its affine Hilbert polynomial `X + 1` has constant
coefficient `1`. -/
theorem ncard_zeroLocus_le_coeff_zero_affineHilbertPolynomial (I : Ideal (MvPolynomial σ k))
    [Module.Finite k (MvPolynomial σ k ⧸ I)] :
    ((zeroLocus K I).ncard : ℚ) ≤ (affineHilbertPolynomial I).coeff 0 := by
  rw [affineHilbertPolynomial_eq_C_finrank, Polynomial.coeff_C_zero]
  exact_mod_cast ncard_zeroLocus_le_finrank_quotient I

/-- For a finite-dimensional coordinate quotient, the zero locus of `I` over any field extension
`K` has at most `affineDegree I` points. The affine degree is then the constant value of the
affine Hilbert polynomial (`affineDegree_of_natDegree_eq_zero`), and the bound is
`ncard_zeroLocus_le_coeff_zero_affineHilbertPolynomial`. The finite-dimensional hypothesis is
needed: over `ZMod 2` in one variable the zero ideal has two zeros and affine degree `1`. -/
theorem ncard_zeroLocus_le_affineDegree (I : Ideal (MvPolynomial σ k))
    [Module.Finite k (MvPolynomial σ k ⧸ I)] :
    ((zeroLocus K I).ncard : ℚ) ≤ affineDegree I := by
  rw [affineDegree_of_natDegree_eq_zero (natDegree_affineHilbertPolynomial_eq_zero_iff.mpr ‹_›)]
  exact ncard_zeroLocus_le_coeff_zero_affineHilbertPolynomial I

/-- If the affine Hilbert polynomial of `I` has natural degree zero, the zero locus of `I` over any
field extension `K` is finite with at most `affineDegree I` points. Natural degree zero makes the
quotient finite-dimensional (`natDegree_affineHilbertPolynomial_eq_zero_iff`). -/
theorem finite_zeroLocus_and_ncard_le_affineDegree (I : Ideal (MvPolynomial σ k))
    (hdeg : (affineHilbertPolynomial I).natDegree = 0) :
    (zeroLocus K I).Finite ∧ ((zeroLocus K I).ncard : ℚ) ≤ affineDegree I :=
  have := natDegree_affineHilbertPolynomial_eq_zero_iff.mp hdeg
  ⟨finite_zeroLocus_of_finite_quotient I, ncard_zeroLocus_le_affineDegree I⟩

end MvPolynomial
