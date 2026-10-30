/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Local/ZeroOrder.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
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
-/

import ThirdParty.ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Coordinates

/-!
# Triangular support at derivative order zero

When the derivative order is zero, the local constraint map has only the variables `T` and `E`.
Every supported monomial satisfies `E ≤ T < m`, so the image lies in a finite-dimensional space
with at most `m * (m + 1) / 2` coordinates. This file gives the exponent set and the resulting
rank bounds for the unrestricted local map and for any restriction of its domain.

## Main statements

* `zeroOrderLocalExponents` and `mem_zeroOrderLocalExponents`: the triangular exponent set.
* `range_localConstraintAt_zeroOrder_le`: the local constraint image is supported on that set.
* `finrank_range_localConstraintAt_zeroOrder_le`: the triangular rank bound.

## References

* [DKT26]
* [BCPZZ26]
-/

open MvPolynomial PolynomialDifferential
open scoped BigOperators Pointwise

namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {R : Type*} [CommRing R]

/-- The local exponent with `T` exponent `t` and `E` exponent `b` at derivative order zero. -/
def zeroOrderLocalExponent (t b : ℕ) : LocalVariable 0 →₀ ℕ :=
  Finsupp.single (localT 0) t + Finsupp.single (localE 0) b

/-- An exponent at derivative order zero is determined by its `T` and `E` exponents. -/
theorem zeroOrderLocalExponent_reconstruct (e : LocalVariable 0 →₀ ℕ) :
    zeroOrderLocalExponent (e (localT 0)) (e (localE 0)) = e := by
  ext v
  cases v with
  | none => simp [zeroOrderLocalExponent, localT, localE, localAux]
  | some v =>
    cases v with
    | none => simp [zeroOrderLocalExponent, localT, localE, localAux]
    | some j => exact Fin.elim0 j

/-- Every supported monomial of an order-zero local constraint has `E ≤ T < m`. -/
theorem localConstraintAt_zeroOrder_support (m : ℕ) (center received : R)
    (Q : DifferentialPolynomial R 0) (e : LocalVariable 0 →₀ ℕ)
    (he : e ∈ (localConstraintAt (d := 0) m center received Q).support) :
    e (localE 0) ≤ e (localT 0) ∧ e (localT 0) < m := by
  obtain ⟨hc, hs⟩ := mem_support_of_mem_support_localConstraintAt he
  refine ⟨localE_le_localT_of_mem_support center received Q hs, ?_⟩
  rw [localContactOrder_eq] at hc
  simpa [localT] using hc

end
end ReedSolomon.HiddenDerivative
