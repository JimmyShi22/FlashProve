/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/Polynomial/Differential/BaseChange.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 5 of the 17 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.Data.Polynomial.Differential.JetDegree
import ThirdParty.ArkLib.ToMathlib.MvPolynomial.PolynomialCoefficients
import ThirdParty.MathlibBackport.Algebra.Polynomial.HasseDeriv

/-!
# Changing the coefficient ring of a differential equation

Let `f : F →+* E` be a ring homomorphism and `Q` a differential polynomial over `F`. Mapping
coefficients commutes with differential specialization,

  `(Q(X, P, D¹P, ..., DᵈP)).map f = (Q.map f)(X, P.map f, D¹(P.map f), ...)`,

so every solution of `Q = 0` of degree at most `D` maps to a solution of `Q.map f = 0` of degree at
most `D`. When `f` is injective this map of solutions is injective, and the individual jet
degrees of `Q` and the cast hypothesis `JetDegreeCastsNeZero` are preserved. Over a finite `E` this
gives `Nat.card (BoundedSolution Q D) ≤ Nat.card (BoundedSolution (Q.map f) D)`: a root count
proved over a larger finite field, such as `FiniteField.Extension F p n`, bounds the root count
over `F`. The inequality is one-way: the equation `0 = 0` with `D = 0` has `2` constant solutions
over `ZMod 2` and `4` over the field with four elements.

Passing to an extension field `E` of `F` does not change the characteristic
(`Algebra.ringChar_eq`), so it does not weaken the characteristic hypotheses of the root counts.
The root counts over extension fields that use these transports are in
`ArkLib.Data.Polynomial.Differential.TotalJetDegreeCount`.

For equations whose coefficients are polynomials in a challenge, `challengeSpecialization` fixes
the challenge before substituting the polynomial and its Hasse derivatives. Coefficient maps
commute with this two-stage specialization and do not increase the challenge-height bound.

## Main statements

* `challengeSpecialization`: specialize a challenge value.
* `challengeSpecialization_map_coefficients`, `MvPolynomial.CoeffNatDegreeLE.map_coefficients`,
  `map_symbolicDifferentialSpecialization`: transport challenge equations and coefficient bounds.
* `map_differentialSpecialization`, `map_separant`: naturality of specialization and separants.
* `map_differentialSpecialization_ne_zero_iff`: injective maps preserve nonvanishing of a
  differential specialization.
* `map_regularSolutionFamily`: bounded regular solution families map to bounded regular
  solution families.
* `jetDegree_map_eq`, `jetTotalDegree_map_eq`, `jetDegreeCastsNeZero_map_iff`: injective
  coefficient maps preserve individual and total jet degrees and the cast hypothesis.
* `jetDegree_map_le`, `jetTotalDegree_map_le`, `highestActiveJet_map_eq_none`: any coefficient map
  does not increase jet degrees, so it keeps an equation with no active jet free of jet variables.
* `BoundedSolution.instFinite`: over a finite coefficient semiring there are finitely many
  solutions of degree at most `D`.
* `BoundedSolution.map`, `BoundedSolution.map_injective`, `BoundedSolution.natCard_le_natCard_map`:
  transport of bounded solutions and the cardinality comparison.

## References

* [DKT26]
-/

namespace PolynomialDifferential

noncomputable section

open Polynomial

variable {F E : Type*} {d : ℕ}

/-- Specialize the polynomial coefficients of a multivariate equation at a challenge value. -/
def challengeSpecialization {F σ : Type*} [CommSemiring F]
    (Q : MvPolynomial σ F[X]) (z : F) : MvPolynomial σ F :=
  MvPolynomial.map (Polynomial.aeval z).toRingHom Q

/-- Specializing after mapping the challenge coefficients agrees with mapping after
specialization. -/
theorem challengeSpecialization_map_coefficients {F E σ : Type*}
    [CommSemiring F] [CommSemiring E] (ι : F →+* E)
    (Q : MvPolynomial σ F[X]) (z : F) :
    challengeSpecialization (MvPolynomial.map (Polynomial.mapRingHom ι) Q) (ι z) =
      MvPolynomial.map ι (challengeSpecialization Q z) := by
  unfold challengeSpecialization
  rw [MvPolynomial.map_map, MvPolynomial.map_map]
  have hc : (Polynomial.aeval (ι z)).toRingHom.comp (Polynomial.mapRingHom ι) =
      ι.comp (Polynomial.aeval z).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp
    · simp
  rw [hc]

/-! ### Naturality -/

/-- Differential specialization commutes with mapping coefficients along a ring homomorphism:
mapping `Q(X, P, D¹P, ..., DᵈP)` along `f` gives `Q.map f` specialized at `P.map f`. This uses
that Hasse derivatives commute with `Polynomial.map`. -/
theorem map_differentialSpecialization [CommSemiring F] [CommSemiring E] (f : F →+* E)
    (Q : DifferentialPolynomial F d) (P : F[X]) :
    (differentialSpecialization Q P).map f =
      differentialSpecialization (MvPolynomial.map f Q) (P.map f) := by
  change Polynomial.mapRingHom f (MvPolynomial.eval₂Hom Polynomial.C _ Q) =
    MvPolynomial.eval₂Hom Polynomial.C _ (MvPolynomial.map f Q)
  rw [MvPolynomial.map_eval₂Hom, MvPolynomial.eval₂Hom_map_hom]
  refine MvPolynomial.eval₂Hom_congr (RingHom.ext fun a ↦ by simp) (funext fun v ↦ ?_) rfl
  cases v <;> simp

/-- Mapping a differential specialization commutes with specializing its challenge first. -/
theorem map_symbolicDifferentialSpecialization {F E : Type*}
    [CommSemiring F] [CommSemiring E] {r : ℕ} (ι : F →+* E)
    (Q : DifferentialPolynomial F[X] r) (z : F) (P : F[X]) :
    (differentialSpecialization (challengeSpecialization Q z) P).map ι =
      differentialSpecialization
        (challengeSpecialization (MvPolynomial.map (Polynomial.mapRingHom ι) Q) (ι z))
        (P.map ι) := by
  rw [challengeSpecialization_map_coefficients, map_differentialSpecialization]

/-- Any coefficient map, injective or not, does not increase an individual jet degree. -/
theorem jetDegree_map_le [CommSemiring F] [CommSemiring E] (f : F →+* E)
    (Q : DifferentialPolynomial F d) (j : Fin (d + 1)) :
    jetDegree (MvPolynomial.map f Q) j ≤ jetDegree Q j :=
  MvPolynomial.degreeOf_le_iff.mpr fun _ hu ↦
    MvPolynomial.monomial_le_degreeOf (some j) (MvPolynomial.support_map_subset f Q hu)

/-! ### Bounded solutions -/

end

end PolynomialDifferential
