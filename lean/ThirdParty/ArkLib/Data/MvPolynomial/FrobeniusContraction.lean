/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/MvPolynomial/FrobeniusContraction.lean, commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13.
Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 2 of the 6 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.Data.Polynomial.FrobeniusContraction
import ThirdParty.ArkLib.ToMathlib.MvPolynomial.RootContraction

/-!
# Frobenius contraction in one variable of a multivariate polynomial

View a polynomial `F` in the variables `Option σ` as a univariate polynomial in the distinguished
variable `none` through `MvPolynomial.optionEquivLeft`. Let the coefficient ring `R` have no zero
divisors and characteristic `p`. If `F` is irreducible of positive degree in `none`, then
`F = rootExpansion (p ^ e) G` for an irreducible `G` whose partial derivative in `none` is
nonzero. The degree of `G` in `none` times `p ^ e` is the degree of `F` in `none`, and the degree
of `G` in every other variable is at most that of `F`. The same holds in exponential
characteristic `p`; in characteristic zero `p = 1` and `G = F`.

When `R` is a unique factorization domain, the polynomial ring `MvPolynomial σ R` is a GCD
domain. An irreducible `G` of positive degree in `none` then stays irreducible over the fraction
field of `MvPolynomial σ R` by Gauss's lemma, and it is separable there when its partial
derivative in `none` is nonzero.

## Main statements

* `MvPolynomial.exists_irreducible_frobeniusContraction`: the terminal contraction in
  characteristic `p`.
* `MvPolynomial.exists_irreducible_frobeniusContraction_expChar`: the same in exponential
  characteristic `p`.
* `MvPolynomial.irreducible_map_optionEquivLeft_fractionRing` and
  `MvPolynomial.separable_map_optionEquivLeft_fractionRing`: passage to the fraction field of the
  coefficient ring.
* `MvPolynomial.exists_frobeniusContraction_fractionRing`: over a unique factorization domain,
  the terminal polynomial is irreducible and separable over that fraction field.
-/

namespace MvPolynomial

variable {R σ : Type*} [CommRing R]

/-- Transport of a univariate Frobenius contraction of `optionEquivLeft R σ F` to `F`. -/
private theorem frobeniusContraction_of_optionEquivLeft {s : ℕ} (hs : s ≠ 0)
    {F : MvPolynomial (Option σ) R} {H : Polynomial (MvPolynomial σ R)}
    (hder : Polynomial.derivative H ≠ 0)
    (hHF : Polynomial.expand (MvPolynomial σ R) s H = optionEquivLeft R σ F)
    (hdeg : H.natDegree * s = (optionEquivLeft R σ F).natDegree)
    (hpos : 0 < H.natDegree) (hirr : Irreducible H) :
    pderiv none ((optionEquivLeft R σ).symm H) ≠ 0 ∧
      rootExpansion s ((optionEquivLeft R σ).symm H) = F ∧
      ((optionEquivLeft R σ).symm H).degreeOf none * s = F.degreeOf none ∧
      0 < ((optionEquivLeft R σ).symm H).degreeOf none ∧
      Irreducible ((optionEquivLeft R σ).symm H) ∧
      ∀ j : σ, ((optionEquivLeft R σ).symm H).degreeOf (some j) ≤ F.degreeOf (some j) := by
  have hG : optionEquivLeft R σ ((optionEquivLeft R σ).symm H) = H :=
    AlgEquiv.apply_symm_apply _ H
  have hcontract : (optionEquivLeft R σ).symm H = rootContraction s F := by
    rw [rootContraction, ← hHF, Polynomial.contract_expand s hs]
  refine ⟨?_, ?_, ?_, ?_, hirr.map (optionEquivLeft R σ).symm, fun j ↦ ?_⟩
  · intro hzero
    apply hder
    rw [← hG, ← optionEquivLeft_pderiv_none, hzero, map_zero]
  · rw [rootExpansion, hG, hHF, AlgEquiv.symm_apply_apply]
  · rw [← natDegree_optionEquivLeft, hG, hdeg, natDegree_optionEquivLeft]
  · rwa [← natDegree_optionEquivLeft, hG]
  · rw [hcontract]
    exact degreeOf_rootContraction_some_le hs F j

section NoZeroDivisors

variable [NoZeroDivisors R] (p : ℕ)

/-- In exponential characteristic `p` without zero divisors, an irreducible polynomial `F` of
positive degree in `none` is `rootExpansion (p ^ e) G` for an irreducible `G` with nonzero partial
derivative in `none`. The degree of `G` in `none` times `p ^ e` is the degree of `F` in `none`,
and the degree of `G` in every variable `some j` is at most that of `F`. -/
theorem exists_irreducible_frobeniusContraction_expChar [ExpChar R p]
    {F : MvPolynomial (Option σ) R} (hFpos : 0 < F.degreeOf none) (hF : Irreducible F) :
    ∃ e : ℕ, ∃ G : MvPolynomial (Option σ) R,
      pderiv none G ≠ 0 ∧
      rootExpansion (p ^ e) G = F ∧
      G.degreeOf none * p ^ e = F.degreeOf none ∧
      0 < G.degreeOf none ∧
      Irreducible G ∧
      ∀ j : σ, G.degreeOf (some j) ≤ F.degreeOf (some j) := by
  have hPpos : 0 < (optionEquivLeft R σ F).natDegree := by
    rwa [natDegree_optionEquivLeft]
  obtain ⟨e, H, hder, hHF, hdeg, hpos, hirr⟩ :=
    Polynomial.exists_irreducible_frobeniusContraction_expChar p hPpos
      (hF.map (optionEquivLeft R σ))
  have hs : p ^ e ≠ 0 := pow_ne_zero e (expChar_pos R p).ne'
  exact ⟨e, _, frobeniusContraction_of_optionEquivLeft hs hder hHF hdeg hpos hirr⟩

end NoZeroDivisors

section FractionRing

variable [IsDomain R] [UniqueFactorizationMonoid R] {L : Type*} [Field L]
  [Algebra (MvPolynomial σ R) L] [IsFractionRing (MvPolynomial σ R) L]

variable (p : ℕ) [CharP R p]

end FractionRing

end MvPolynomial
