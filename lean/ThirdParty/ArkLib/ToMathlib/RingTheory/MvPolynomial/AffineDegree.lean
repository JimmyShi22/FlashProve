/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/ToMathlib/RingTheory/MvPolynomial/AffineDegree.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 9 of the 12 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertPolynomial

/-!
# The affine degree of an ideal

Let `k` be a field, `σ` a finite type and `I` an ideal of `MvPolynomial σ k`. Write
`P = MvPolynomial.affineHilbertPolynomial I` and `d = natDegree P`. The affine degree of `I` is
`d! * leadingCoeff P`, a rational number. For large `N` the affine Hilbert function is
`affineDegree I * N ^ d / d! + O(N ^ (d - 1))`, so `affineDegree I` is the normalized leading
term of the growth of the quotient `MvPolynomial σ k ⧸ I` under the total-degree filtration.

The affine degree is nonnegative, and positive exactly for proper ideals; the unit ideal has
degree `0`. The polynomial ring has degree `1`. A finite-dimensional quotient has degree equal to
its dimension over `k`, and a nonzero principal ideal `span {f}` has degree `totalDegree f`.
Along an inclusion `I ≤ J` of ideals whose polynomials have the same natural degree, the degree
of `J` is at most that of `I`.

The bound on the number of points of a zero-dimensional zero locus by the affine degree is
`MvPolynomial.ncard_zeroLocus_le_affineDegree` in
`ArkLib.ToMathlib.RingTheory.Nullstellensatz.AffineHilbertPolynomial`.

## Main statements

* `MvPolynomial.affineDegree`: the definition.
* `MvPolynomial.affineDegree_nonneg`, `MvPolynomial.affineDegree_pos_iff`,
  `MvPolynomial.affineDegree_top`: sign.
* `MvPolynomial.affineDegree_bot`: the polynomial ring has degree `1`.
* `MvPolynomial.affineDegree_eq_finrank`: finite-dimensional quotients.
* `MvPolynomial.affineDegree_span_singleton`: hypersurfaces.
* `MvPolynomial.affineDegree_le_of_le`: comparison along inclusions of the same dimension.
* `MvPolynomial.affineDegree_le_of_eventually_affineHilbertFunction_le`: an upper bound from an
  eventual polynomial bound on the affine Hilbert function.
-/

noncomputable section

open Filter Polynomial

namespace MvPolynomial

variable {k σ : Type*} [Field k] [Finite σ]

/-- The affine degree of `I`: `d! * leadingCoeff P`, where `P` is the affine Hilbert polynomial
of `I` and `d` its natural degree. The factor `d!` makes the polynomial ring have degree `1`
(`affineDegree_bot`) and a finite-dimensional quotient have degree equal to its dimension
(`affineDegree_eq_finrank`). -/
def affineDegree (I : Ideal (MvPolynomial σ k)) : ℚ :=
  ((affineHilbertPolynomial I).natDegree.factorial : ℚ) * (affineHilbertPolynomial I).leadingCoeff

/-- The affine degree is nonnegative, because the affine Hilbert polynomial is eventually
nonnegative on the natural numbers and so has a nonnegative leading coefficient. -/
theorem affineDegree_nonneg (I : Ideal (MvPolynomial σ k)) : 0 ≤ affineDegree I :=
  mul_nonneg (Nat.cast_nonneg _)
    (leadingCoeff_nonneg_of_eventually_eval_natCast_nonneg
      (eventually_eval_affineHilbertPolynomial_nonneg I))

/-- The unit ideal has affine degree `0`, since its affine Hilbert polynomial is zero. -/
@[simp]
theorem affineDegree_top : affineDegree (⊤ : Ideal (MvPolynomial σ k)) = 0 := by
  simp [affineDegree]

/-- A proper ideal has positive affine degree, since its affine Hilbert polynomial has positive
leading coefficient. -/
theorem affineDegree_pos {I : Ideal (MvPolynomial σ k)} (hI : I ≠ ⊤) : 0 < affineDegree I :=
  mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _)) (leadingCoeff_affineHilbertPolynomial_pos hI)

/-- The affine degree is positive exactly for proper ideals. -/
theorem affineDegree_pos_iff {I : Ideal (MvPolynomial σ k)} : 0 < affineDegree I ↔ I ≠ ⊤ :=
  ⟨fun h hI ↦ by simp [hI] at h, affineDegree_pos⟩

/-- The affine degree vanishes exactly for the unit ideal. -/
@[simp]
theorem affineDegree_eq_zero_iff {I : Ideal (MvPolynomial σ k)} : affineDegree I = 0 ↔ I = ⊤ := by
  rw [← not_iff_not, ← Ne, ← Ne, ← affineDegree_pos_iff]
  exact ⟨(affineDegree_nonneg I).lt_of_ne', ne_of_gt⟩

/-- When the affine Hilbert polynomial is constant, the affine degree is that constant. -/
theorem affineDegree_of_natDegree_eq_zero {I : Ideal (MvPolynomial σ k)}
    (hdeg : (affineHilbertPolynomial I).natDegree = 0) :
    affineDegree I = (affineHilbertPolynomial I).coeff 0 := by
  rw [affineDegree, hdeg, Nat.factorial_zero, Nat.cast_one, one_mul, leadingCoeff, hdeg]

/-- The polynomial ring has affine degree `1`: in `n` variables its affine Hilbert polynomial
`Polynomial.preHilbertPoly ℚ n 0` has natural degree `n` and leading coefficient `1 / n!`. -/
@[simp]
theorem affineDegree_bot : affineDegree (⊥ : Ideal (MvPolynomial σ k)) = 1 := by
  rw [affineDegree, affineHilbertPolynomial_bot, natDegree_preHilbertPoly,
    leadingCoeff_preHilbertPoly]
  exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

/-- An eventual polynomial bound on the affine Hilbert function bounds the affine degree. If the
affine Hilbert polynomial of `I` has natural degree `d`, a polynomial `R` of natural degree at most
`d` satisfies `H(I, N) ≤ R(N)` for all large `N`, then `affineDegree I ≤ d! * R.coeff d`.

Both polynomials have natural degree at most `d`, so the eventual inequality compares their
coefficients in degree `d` (`Polynomial.coeff_le_of_natDegree_le_of_eventually_eval_natCast_le`).
The equality `hdim` cannot be weakened to an upper bound: for `I = ⊥` in one variable, `d = 2` and
`R = X + 1`, the bound `H(⊥, N) = N + 1 ≤ R(N)` holds, but `affineDegree ⊥ = 1` exceeds
`2! * R.coeff 2 = 0`. -/
theorem affineDegree_le_of_eventually_affineHilbertFunction_le {I : Ideal (MvPolynomial σ k)}
    {d : ℕ} {R : ℚ[X]} (hdim : (affineHilbertPolynomial I).natDegree = d) (hR : R.natDegree ≤ d)
    (hbound : ∀ᶠ N : ℕ in atTop, (affineHilbertFunction I N : ℚ) ≤ R.eval (N : ℚ)) :
    affineDegree I ≤ (d.factorial : ℚ) * R.coeff d := by
  have hc := coeff_le_of_natDegree_le_of_eventually_eval_natCast_le hdim.le hR
    (by
      filter_upwards [eventually_eval_affineHilbertPolynomial I, hbound] with N hN hRN
      rwa [hN])
  rw [affineDegree, hdim, leadingCoeff, hdim]
  exact mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)

end MvPolynomial
