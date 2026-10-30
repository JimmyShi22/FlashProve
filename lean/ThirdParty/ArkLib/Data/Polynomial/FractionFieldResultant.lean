/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/Polynomial/FractionFieldResultant.lean, commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13.
Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 4 of the 7 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
* Comment changed: one doc comment says NormalizedGCDMonoid where ArkLib's says IsGCDMonoid, as the
  changed statement does.
* Statement changed, Polynomial.separable_map_of_irreducible_of_derivative_ne_zero: [IsGCDMonoid R]
  became [NormalizedGCDMonoid R]: this Mathlib has no IsGCDMonoid and states its Gauss lemma with
  NormalizedGCDMonoid.
* Statement changed, Polynomial.resultant_derivative_ne_zero_of_irreducible: [IsGCDMonoid R] became
  [NormalizedGCDMonoid R], for the same reason.
-/

import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.SimpleRing.Principal
import ThirdParty.ArkLib.Data.Polynomial.ResultantSpecialization

/-!
# Separability resultants over a fraction field

The derivative resultant padded to degrees `d` and `d - 1` is nonzero whenever the
polynomial becomes separable over its fraction field. The derivative may have degree
strictly below `d - 1`, as happens for `Y^p - Y` in characteristic `p`.
The actual-degree resultant also provides a Bezout certificate after arbitrary coefficient
maps, including maps that lower polynomial degrees. These two specialization statements are the
case `m = f.natDegree`, `n = g.natDegree` of the declared-degree statements in
`ArkLib.Data.Polynomial.ResultantSpecialization`.

This generalizes the large-characteristic argument in Remco Bloemen's BCHKS formalization,
`ProximityPrize/SubmissionLower/BCHKSConcreteGoodSpecialization.lean`, lines 272–316, at
https://github.com/proximity-prize/proximity-prize/commit/19bc7d3e21b2261257e1961acd720b2c395d87e1.
The proof uses Mathlib's padding identity instead of requiring that differentiation retain
the leading term. No donor proof is copied.

## Irreducible polynomials

`resultant_derivative_ne_zero_of_irreducible`: over a GCD domain `R`, an irreducible `f : R[X]`
with `f.derivative ≠ 0` has `resultant f f.derivative f.natDegree (f.natDegree - 1) ≠ 0`. The
intermediate `separable_map_of_irreducible_of_derivative_ne_zero` gives separability over the
fraction field by Gauss's lemma. This is ported from ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`,
`ArkLib/ToMathlib/Polynomial/SeparableResultant.lean`,
`separableResultant_ne_zero_of_irreducible`, which is stated for `A : F[X][X]` over a field `F`,
with an explicit fraction field and the hypotheses `A.natDegree = b` and `0 < b`. Here the
coefficient ring is any GCD domain, the fraction field is `FractionRing R`, and `0 < b` is
dropped because it follows from `f.derivative ≠ 0`. The source's
`separableResultant A b = resultant A.derivative A (b - 1) b` equals the resultant here by
`resultant_comm_sub_one`.

## References

* [Ben-Sasson, E., Carmon, D., Haböck, U., Kopparty, S., Saraf, S.,
  *On Proximity Gaps for Reed--Solomon Codes*][BCHKS25], Section 3.2.
-/

namespace Polynomial

variable {R K : Type*} [CommRing R]

/-- Padding the derivative degree preserves the nonzero resultant of a separable polynomial.
This also covers nonzero constant polynomials, where both dimensions are zero. -/
theorem resultant_derivative_ne_zero_of_separable [IsDomain R] (f : R[X]) (hsep : f.Separable) :
    resultant f f.derivative f.natDegree (f.natDegree - 1) ≠ 0 := by
  have hf : f ≠ 0 := hsep.ne_zero
  have hdegree := natDegree_derivative_le f
  rw [← Nat.add_sub_of_le hdegree,
    resultant_add_right_deg _ _ _ _ _ le_rfl, coeff_natDegree]
  exact mul_ne_zero (pow_ne_zero _ (leadingCoeff_ne_zero.mpr hf))
    (resultant_ne_zero f f.derivative hsep)

variable [Field K]

variable [Algebra R K] [IsFractionRing R K]

/-- Fraction-field separability gives a nonzero derivative resultant in the original domain.
No ring-level Bezout identity or restriction on the characteristic is assumed. -/
theorem resultant_derivative_ne_zero_of_separable_map_fractionField (f : R[X])
    (hsep : (f.map (algebraMap R K)).Separable) :
    resultant f f.derivative f.natDegree (f.natDegree - 1) ≠ 0 := by
  have hdeg : (f.map (algebraMap R K)).natDegree = f.natDegree :=
    natDegree_map_eq_of_injective (IsFractionRing.injective R K) f
  have hne := resultant_derivative_ne_zero_of_separable _ hsep
  rw [hdeg, derivative_map, resultant_map_map] at hne
  exact fun hz => hne (by rw [hz, map_zero])

/-- Over a GCD domain `R` with fraction field `K`, an irreducible polynomial `f : R[X]` with
nonzero derivative becomes separable over `K`.

A nonzero derivative forces `0 < f.natDegree`, so `f` is primitive (`Irreducible.isPrimitive`),
and Gauss's lemma (`IsPrimitive.irreducible_iff_irreducible_map_fraction_map`) makes `f`
irreducible over `K`. An irreducible polynomial over a field is separable exactly when its
derivative is nonzero. The hypothesis `hder` is needed: over `𝔽₂[t]`, `Y ^ 2 - t` is
irreducible and has derivative `0`. `NormalizedGCDMonoid R` is the hypothesis of Mathlib's Gauss lemma
for primitive, not necessarily monic, polynomials. -/
theorem separable_map_of_irreducible_of_derivative_ne_zero [IsDomain R] [NormalizedGCDMonoid R]
    (f : R[X]) (hirr : Irreducible f) (hder : f.derivative ≠ 0) :
    (f.map (algebraMap R K)).Separable := by
  have hdeg : f.natDegree ≠ 0 := fun h ↦ hder (by
    rw [eq_C_of_natDegree_eq_zero h, derivative_C])
  have hmap : Irreducible (f.map (algebraMap R K)) :=
    ((hirr.isPrimitive hdeg).irreducible_iff_irreducible_map_fraction_map).mp hirr
  refine (separable_iff_derivative_ne_zero hmap).mpr ?_
  rw [derivative_map]
  exact (Polynomial.map_ne_zero_iff (IsFractionRing.injective R K)).mpr hder

/-- Over a GCD domain `R`, an irreducible polynomial `f : R[X]` with nonzero derivative has a
nonzero padded derivative resultant: `resultant f f.derivative f.natDegree (f.natDegree - 1) ≠ 0`.

This combines `separable_map_of_irreducible_of_derivative_ne_zero` over `FractionRing R` with
`resultant_derivative_ne_zero_of_separable_map_fractionField`. Both hypotheses are needed.
Irreducibility: `Y ^ 2` over `ℚ[t]` has nonzero derivative `2 * Y` and a common root `0` with
it. Nonzero derivative: `Y ^ 2 - t` over `𝔽₂[t]` is irreducible and its derivative is `0`, so the
resultant vanishes. The degree `0 < f.natDegree` is not a separate hypothesis, because a constant
has derivative `0`. The derivative may have degree below `f.natDegree - 1`. The theorem applies
with `R = F[X]` for a field `F`, which is the bivariate case. -/
theorem resultant_derivative_ne_zero_of_irreducible [IsDomain R] [NormalizedGCDMonoid R]
    (f : R[X]) (hirr : Irreducible f) (hder : f.derivative ≠ 0) :
    resultant f f.derivative f.natDegree (f.natDegree - 1) ≠ 0 :=
  resultant_derivative_ne_zero_of_separable_map_fractionField (K := FractionRing R) f
    (separable_map_of_irreducible_of_derivative_ne_zero f hirr hder)

end Polynomial
