/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/ToMathlib/MvPolynomial/FrobeniusPullback.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 8 of the 17 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.MvPolynomial.Expand

/-!
# Inverse Frobenius coefficient twist and variable power substitution

Let `R` be a perfect ring of exponential characteristic `p`, and let `s = p ^ e`. For a
multivariate polynomial `G` over `R`, the inverse Frobenius coefficient twist
`inverseFrobeniusTwist p e G` applies the inverse of `x ↦ x ^ s` to every coefficient of `G`.
Raising it to the power `s` gives `G.expand s`, the substitution of `X i ^ s` for every
variable. Consequently a point `v` with `G (v ^ s) = 0` is a root of the twist.

The substitution of `X i ^ q i` for each variable `X i`, with variable-dependent exponents `q`, is
`variablePowerSubstitution q`. Exponent functions compose by pointwise multiplication. If
`F = variablePowerSubstitution r G` substitutes powers into some variables of `G`, and `q` supplies
the complementary exponents with `q i * r i = s` for every `i`, then the `s`-th power of the twist
of `G` is `variablePowerSubstitution q F`. With three variables and `r` the exponent `s` on the
last variable only, this is the identity `G̃(T, W, U) ^ s = F(T ^ s, W ^ s, U)` for
`F(X, Z, Y) = G(X, Z, Y ^ s)`.

The twist is `MvPolynomial.map` along a ring automorphism, so it preserves irreducibility, every
individual degree, and commutes with partial derivatives.

## Main statements

* `MvPolynomial.inverseFrobeniusTwist_pow`:
  `inverseFrobeniusTwist p e G ^ p ^ e = G.expand (p ^ e)`.
* `MvPolynomial.eval_inverseFrobeniusTwist_eq_zero`: root transport along the twist.
* `MvPolynomial.variablePowerSubstitution_comp` and `MvPolynomial.eval_variablePowerSubstitution`.
* `MvPolynomial.inverseFrobeniusTwist_pow_eq_variablePowerSubstitution` and
  `MvPolynomial.eval_inverseFrobeniusTwist_eq_zero_of_variablePowerSubstitution`: the identity
  and root transport for a split between complementary exponents.
* `MvPolynomial.irreducible_inverseFrobeniusTwist_iff`,
  `MvPolynomial.degreeOf_inverseFrobeniusTwist` and `MvPolynomial.pderiv_inverseFrobeniusTwist`.
* `MvPolynomial.degreeOf_map_of_injective`: an injective coefficient map preserves every
  individual degree.
-/

namespace MvPolynomial

noncomputable section

section MapDegree

variable {R S σ : Type*} [CommSemiring R] [CommSemiring S]

/-- An injective coefficient map preserves the degree in every variable. -/
theorem degreeOf_map_of_injective {f : R →+* S} (hf : Function.Injective f)
    (G : MvPolynomial σ R) (i : σ) : degreeOf i (map f G) = degreeOf i G := by
  classical
  simp only [degreeOf_def, degrees_map_of_injective G hf]

end MapDegree

section VariablePowerSubstitution

variable {R τ : Type*} [CommSemiring R]

end VariablePowerSubstitution

section InverseFrobeniusTwist

variable {R σ : Type*} [CommSemiring R] (p e : ℕ) [ExpChar R p] [PerfectRing R p]

/-- Apply the inverse of the `e`-fold Frobenius `x ↦ x ^ p ^ e` to every coefficient. -/
def inverseFrobeniusTwist (G : MvPolynomial σ R) : MvPolynomial σ R :=
  G.map (iterateFrobeniusEquiv R p e).symm

/-- The `p ^ e`-th power of the inverse Frobenius coefficient twist is the substitution of
`X i ^ p ^ e` for every variable. -/
theorem inverseFrobeniusTwist_pow (G : MvPolynomial σ R) :
    inverseFrobeniusTwist p e G ^ p ^ e = G.expand (p ^ e) := by
  have hcomp : (iterateFrobenius R p e).comp (iterateFrobeniusEquiv R p e).symm =
      RingHom.id R := by
    ext x
    exact (iterateFrobeniusEquiv R p e).apply_symm_apply x
  simpa only [inverseFrobeniusTwist, map_expand, map_map, hcomp, map_id] using
    (map_iterateFrobenius_expand p (inverseFrobeniusTwist p e G) e).symm

/-- The inverse Frobenius coefficient twist vanishes only at zero. -/
theorem inverseFrobeniusTwist_eq_zero_iff {G : MvPolynomial σ R} :
    inverseFrobeniusTwist p e G = 0 ↔ G = 0 :=
  map_eq_zero_iff _ (map_injective _ (iterateFrobeniusEquiv R p e).symm.injective)

/-- The inverse Frobenius coefficient twist is irreducible exactly when the polynomial is. -/
theorem irreducible_inverseFrobeniusTwist_iff {G : MvPolynomial σ R} :
    Irreducible (inverseFrobeniusTwist p e G) ↔ Irreducible G :=
  MulEquiv.irreducible_iff (mapEquiv σ (iterateFrobeniusEquiv R p e).symm)

/-- The inverse Frobenius coefficient twist preserves the degree in every variable. -/
theorem degreeOf_inverseFrobeniusTwist (G : MvPolynomial σ R) (i : σ) :
    degreeOf i (inverseFrobeniusTwist p e G) = degreeOf i G :=
  degreeOf_map_of_injective (iterateFrobeniusEquiv R p e).symm.injective G i

/-- The inverse Frobenius coefficient twist commutes with every partial derivative. -/
theorem pderiv_inverseFrobeniusTwist (G : MvPolynomial σ R) (i : σ) :
    pderiv i (inverseFrobeniusTwist p e G) = inverseFrobeniusTwist p e (pderiv i G) :=
  pderiv_map

/-- A partial derivative of the twist is nonzero exactly when that partial derivative of the
polynomial is nonzero. -/
theorem pderiv_inverseFrobeniusTwist_ne_zero_iff (G : MvPolynomial σ R) (i : σ) :
    pderiv i (inverseFrobeniusTwist p e G) ≠ 0 ↔ pderiv i G ≠ 0 := by
  rw [pderiv_inverseFrobeniusTwist, ne_eq, inverseFrobeniusTwist_eq_zero_iff]

end InverseFrobeniusTwist

end

end MvPolynomial
