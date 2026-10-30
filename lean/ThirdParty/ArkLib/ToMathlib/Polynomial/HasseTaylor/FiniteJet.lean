/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/ToMathlib/Polynomial/HasseTaylor/FiniteJet.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 8 of the 30 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Finite Hasse jets of univariate polynomials

This file packages Mathlib's Hasse derivatives into finite coordinate vectors.  The construction is
valid over arbitrary semirings and therefore does not silently introduce factorial denominators or
characteristic assumptions.

The main declarations are:

* `Polynomial.hasseCoeffAt`: the `i`-th Hasse derivative evaluated at a point;
* `Polynomial.hasseJet`: the first `m` Hasse coefficients at a point, as a linear map;
* `Polynomial.hasseDerivDegreeLT`: the degree-lowering Hasse derivative on `degreeLT`;
* `Polynomial.hasseJetEquiv`: over a commutative ring, finite jets give coordinates on
  polynomials of degree strictly less than `m`.
-/

namespace Polynomial

noncomputable section

variable {R : Type*}

section Semiring

variable [Semiring R]

/-! ### Finite Hasse coordinates -/

/-- The `i`-th Hasse coefficient of `p` at `r`, packaged as a linear functional.

Equivalently, this is coefficient `i` of `p(X + r)`. -/
def hasseCoeffAt (r : R) (i : ℕ) : R[X] →ₗ[R] R :=
  (leval r).comp (hasseDeriv i)

@[simp]
theorem hasseCoeffAt_apply (r : R) (i : ℕ) (p : R[X]) :
    hasseCoeffAt r i p = (hasseDeriv i p).eval r :=
  rfl

/-- The first `m` Hasse coefficients of a polynomial at `r`.

Index `i : Fin m` records `D⁽ⁱ⁾ p(r)`, where `D⁽ⁱ⁾` is the Hasse derivative.  Thus
`m = 0` gives the empty jet and `m = 1` records only evaluation at `r`. -/
def hasseJet (m : ℕ) (r : R) : R[X] →ₗ[R] (Fin m → R) where
  toFun p i := hasseCoeffAt r i p
  map_add' p q := by
    ext i
    simp
  map_smul' c p := by
    ext i
    simp

@[simp]
theorem hasseJet_apply (m : ℕ) (r : R) (p : R[X]) (i : Fin m) :
    hasseJet m r p i = (hasseDeriv i p).eval r :=
  rfl

@[simp]
theorem hasseJet_zero_apply (m : ℕ) (r : R) (p : R[X]) :
    hasseJet (m + 1) r p 0 = p.eval r := by
  simp

@[simp]
theorem hasseJet_zero (r : R) (p : R[X]) : hasseJet 0 r p = 0 :=
  Subsingleton.elim _ _

@[simp]
theorem hasseJet_one (r : R) (p : R[X]) : hasseJet 1 r p = fun _ ↦ p.eval r := by
  ext i
  simp [Fin.eq_zero i]

/-- Finite Hasse jets are precisely the initial coefficients of the Taylor shift. -/
theorem hasseJet_eq_taylor_coeff (m : ℕ) (r : R) (p : R[X]) (i : Fin m) :
    hasseJet m r p i = (taylor r p).coeff i := by
  rw [hasseJet_apply, taylor_coeff]

/-! ### Degree-lowering Hasse derivatives -/

end Semiring

section CommSemiring

variable [CommSemiring R]

/-! ### Products, shifts, and affine substitutions -/

end CommSemiring

section CommRing

variable [CommRing R]

/-! ### Finite-jet coordinates for degree-bounded polynomials -/

end CommRing

end

end Polynomial
