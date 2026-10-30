/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Quang Dao, Justin Thaler
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Local/ConstraintMap.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 16 of the 30 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import ThirdParty.ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Index
import ThirdParty.ArkLib.Data.CodingTheory.HiddenDerivative.Substitution
import ThirdParty.ArkLib.Data.MvPolynomial.WeightedOrder

/-!
# Linear maps for the hidden-derivative local constraints

This file defines the homogeneous linear constraints that a differential polynomial must satisfy
at one received point `(center, received)`. After the unscaled local substitution, the
constraint is that every monomial `T^i E^b Y^c` of contact order `i + d * b < m` has coefficient
zero. `localConstraintAt` returns the part of the substituted polynomial that must vanish, and
`localConstraintCoordinatesAt` returns the same coefficients as a vector.

The point-dependent map factors through a map that does not depend on the point: first
translate `X = center + T`, `Y₀ = received + T U` and reduce modulo `T^m`
(`translatedLocalTruncation`), then rewrite `U = E + localJetSum d` and keep the low-contact
part (`enlargedLocalConstraintMap`). The reduction modulo `T^m` before the rewrite does not
change the result, because the rewrite sends every generator of `T`-weight `t` to a polynomial
of contact order at least `t`. This is an instance of
`MvPolynomial.weightedTruncation_bind₁_weightedTruncation`. The factorization is what the local
rank bounds in `Interpolation/Local/Rank.lean` use: every local constraint map on the exact
interpolation space factors through one fixed linear map.

All maps are linear over an arbitrary commutative ring `R`.

## Main statements

* `satisfiesLocalConstraints_iff_coordinates_eq_zero` and
  `satisfiesLocalConstraints_iff_coeff_eq_zero`: the polynomial, coordinate, and coefficient
  forms of the local constraints agree.
* `map_projectLowContact` and `map_unscaledLocalSubstitution`: both operations commute with
  changing coefficients.
* `enlargedLocalConstraintMap_truncateLocalT`: reducing modulo `T^m` before the rewrite does not
  change the enlarged constraints.
* `localConstraintAt_eq_enlarged_comp_translated`: the point-dependent map is
  `enlargedLocalConstraintMap m ∘ translatedLocalTruncation m center received`.
* `map_localConstraintAt`: changing coefficients commutes with the local constraint map and maps
  its point.
* `exactLocalConstraintAt_eq_enlarged_comp`: the same factorization on the exact interpolation
  space.
* `SatisfiesLocalConstraints.map`: coefficient changes preserve the local constraints.
* `globalExactCoefficientConstraintMap`: all local constraints, over an arbitrary index type of
  received points, as one linear map on exact interpolation coefficients.

Parts of this file are adapted, with permission, from Kai Zhe Zheng's `kz99/rs-ld-mca`
formalization.

## References

* [BCPZZ26]
* [DKT26]
-/

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R]
variable {d D A M W : ℕ}

/-! ### Coefficient projections -/

/-- Keep the monomials of contact order below `m`. -/
def projectLowContact (m : ℕ) : LocalPolynomial R d →ₗ[R] LocalPolynomial R d :=
  weightedTruncation (localContactWeight d) m

/-- The coefficient of `projectLowContact m F` at `e` is that of `F` if `e` has contact order
below `m`, and zero otherwise. -/
@[simp]
theorem coeff_projectLowContact (m : ℕ) (F : LocalPolynomial R d)
    (e : LocalVariable d →₀ ℕ) :
    (projectLowContact (R := R) m F).coeff e =
      if localContactOrder d e < m then F.coeff e else 0 :=
  coeff_weightedTruncation _ m F e

/-- Changing coefficients commutes with projection to contact order below `m`. -/
theorem map_projectLowContact {S : Type*} [CommRing S] (φ : R →+* S) (m : ℕ)
    (P : LocalPolynomial R d) :
    MvPolynomial.map φ (projectLowContact m P) =
      projectLowContact m (MvPolynomial.map φ P) := by
  ext e
  rw [coeff_map, coeff_projectLowContact, coeff_projectLowContact]
  rw [coeff_map]
  by_cases he : localContactOrder d e < m <;> simp [he]

/-- Exponents of contact order below `m`. This type is empty for `m = 0` and infinite for `m > 0`:
the visible jets have contact weight zero, and so does `E` when `d = 0`, so every power of `Y₁`
(for `d > 0`) or of `E` (for `d = 0`) has contact order `0`. -/
abbrev LowContactIndex (d m : ℕ) :=
  {e : LocalVariable d →₀ ℕ // localContactOrder d e < m}

/-- All coefficients of contact order below `m`, as a vector indexed by `LowContactIndex d m`. -/
def lowContactCoefficients (m : ℕ) :
    LocalPolynomial R d →ₗ[R] (LowContactIndex d m → R) :=
  LinearMap.pi fun e : LowContactIndex d m => lcoeff R e.1

/-- The low-contact part vanishes exactly when every coefficient of contact order below `m`
vanishes. -/
theorem projectLowContact_eq_zero_iff (m : ℕ) (F : LocalPolynomial R d) :
    projectLowContact (R := R) m F = 0 ↔
      ∀ e, localContactOrder d e < m → F.coeff e = 0 :=
  filterSupport_eq_zero_iff _ F

/-- The low-contact coefficient vector vanishes exactly when every coefficient of contact order
below `m` vanishes. -/
theorem lowContactCoefficients_eq_zero_iff (m : ℕ) (F : LocalPolynomial R d) :
    lowContactCoefficients (R := R) m F = 0 ↔
      ∀ e, localContactOrder d e < m → F.coeff e = 0 := by
  constructor
  · intro h e he
    simpa [lowContactCoefficients] using congrFun h ⟨e, he⟩
  · intro h
    ext e
    simpa [lowContactCoefficients] using h e.1 e.2

/-- The polynomial and coordinate forms of the low-contact projection have the same kernel. -/
theorem projectLowContact_eq_zero_iff_lowContactCoefficients_eq_zero
    (m : ℕ) (F : LocalPolynomial R d) :
    projectLowContact (R := R) m F = 0 ↔ lowContactCoefficients (R := R) m F = 0 := by
  rw [projectLowContact_eq_zero_iff, lowContactCoefficients_eq_zero_iff]

/-! ### Point-dependent and enlarged maps -/

/-- The point-independent map: rewrite `U = E + localJetSum d`, then keep the monomials of
contact order below `m`. -/
def enlargedLocalConstraintMap (m : ℕ) : LocalPolynomial R d →ₗ[R] LocalPolynomial R d :=
  (projectLowContact m).comp (rewriteUToE d).toLinearMap

/-- The local constraint map at `(center, received)`: the low-contact part of the unscaled local
substitution. -/
def localConstraintAt (m : ℕ) (center received : R) :
    DifferentialPolynomial R d →ₗ[R] LocalPolynomial R d :=
  (projectLowContact m).comp (unscaledLocalSubstitution d center received).toLinearMap

/-- Changing coefficients commutes with unscaled local substitution and maps its point. -/
theorem map_unscaledLocalSubstitution {S : Type*} [CommRing S] (φ : R →+* S)
    (center received : R) (Q : DifferentialPolynomial R d) :
    MvPolynomial.map φ (unscaledLocalSubstitution d center received Q) =
      unscaledLocalSubstitution d (φ center) (φ received) (MvPolynomial.map φ Q) := by
  have hhom : (MvPolynomial.map φ).comp
      (unscaledLocalSubstitution d center received).toRingHom =
      (unscaledLocalSubstitution d (φ center) (φ received)).toRingHom.comp
        (MvPolynomial.map φ) := by
    refine MvPolynomial.ringHom_ext (fun a => by simp) fun v => ?_
    rcases v with _ | j
    · simp
    · refine Fin.cases ?_ (fun i => ?_) j
      · simp [localCorrection]
      · simp
  exact RingHom.congr_fun hhom Q

/-- The local constraints at `(center, received)` as a coefficient vector. -/
def localConstraintCoordinatesAt (m : ℕ) (center received : R) :
    DifferentialPolynomial R d →ₗ[R] (LowContactIndex d m → R) :=
  (lowContactCoefficients m).comp (unscaledLocalSubstitution d center received).toLinearMap

/-- `Q` satisfies the local constraints of multiplicity `m` at `(center, received)`: after the
unscaled local substitution, every monomial of contact order below `m` has coefficient zero. -/
def SatisfiesLocalConstraints (m : ℕ) (center received : R)
    (Q : DifferentialPolynomial R d) : Prop :=
  localConstraintAt m center received Q = 0

/-- The local constraints hold exactly when their coordinate vector vanishes. -/
theorem satisfiesLocalConstraints_iff_coordinates_eq_zero
    (m : ℕ) (center received : R) (Q : DifferentialPolynomial R d) :
    SatisfiesLocalConstraints m center received Q ↔
      localConstraintCoordinatesAt m center received Q = 0 :=
  projectLowContact_eq_zero_iff_lowContactCoefficients_eq_zero m _

/-- The local constraints hold exactly when every low-contact coefficient of the substituted
polynomial vanishes. -/
theorem satisfiesLocalConstraints_iff_coeff_eq_zero
    (m : ℕ) (center received : R) (Q : DifferentialPolynomial R d) :
    SatisfiesLocalConstraints m center received Q ↔
      ∀ e, localContactOrder d e < m →
        (unscaledLocalSubstitution d center received Q).coeff e = 0 :=
  projectLowContact_eq_zero_iff m _

/-- Local constraints are preserved by every coefficient-ring homomorphism. -/
theorem SatisfiesLocalConstraints.map {S : Type*} [CommRing S] (φ : R →+* S) (m : ℕ)
    (center received : R) (Q : DifferentialPolynomial R d)
    (hQ : SatisfiesLocalConstraints m center received Q) :
    SatisfiesLocalConstraints m (φ center) (φ received) (MvPolynomial.map φ Q) := by
  rw [SatisfiesLocalConstraints, localConstraintAt, LinearMap.comp_apply,
    AlgHom.toLinearMap_apply] at hQ ⊢
  rw [← map_unscaledLocalSubstitution, ← map_projectLowContact]
  simpa using congrArg (MvPolynomial.map φ) hQ

/-! ### Truncation factorization -/

/-! ### Exact interpolation coordinates -/

end ReedSolomon.HiddenDerivative
