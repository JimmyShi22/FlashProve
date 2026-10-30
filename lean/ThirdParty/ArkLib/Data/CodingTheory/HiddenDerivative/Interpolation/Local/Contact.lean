/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Local/Contact.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* All 3 declarations of the file are kept. ArkLib's comment at the top of the file is unchanged.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.ConstraintMap
import ThirdParty.ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.Identity
import ThirdParty.ArkLib.ToMathlib.Polynomial.HasseTaylor.Lifting

/-!
# Local constraints force contact of order `m`

The local constraints of order `m` at an evaluation point `(center, received)` say that every
monomial of contact order below `m` has coefficient zero in the unscaled local substitution of
`Q`; contact order gives `T` weight `1`, the hidden error `E` weight `d`, and the visible jets
weight `0`. This file shows that the constraints force `(X - center) ^ m` to divide
`Q(X, P, D¹P, ..., DᵈP)` for every polynomial `P` with `P(center) = received`.

The argument evaluates the unscaled local substitution at `T ↦ X`, `E ↦` the normalized backward
Taylor error of `P` (divisible by `X ^ d`), and the shifted higher Hasse derivatives of `P`. By
`localPolynomialEvaluation_unscaled_backwardError` this evaluation is the shifted-jet
substitution of `Q` at `P`, and by `MvPolynomial.pow_dvd_eval₂Hom_of_mem_restrictWeightedOrder` a
polynomial of contact order at least `m` evaluates to a multiple of `X ^ m`. No hypothesis on the
commutative ring is needed.

## Main statements

* `X_pow_dvd_localPolynomialEvaluation_of_lowContact`: local polynomials with no monomial of
  contact order below `m` evaluate to multiples of `X ^ m` when the error is divisible by
  `X ^ d`.
* `X_pow_dvd_shiftedJetSubstitution_of_contact` and
  `X_sub_C_pow_dvd_differentialSpecialization_of_contact`: the local constraints force contact of
  order `m` at every agreement point.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26], Section 3.5, Definition 3.7 and Lemma 3.8.
-/

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R] {d m : ℕ}

/-- Let `F` be a local polynomial whose monomials of contact order below `m` all have coefficient
zero. Evaluating `F` at `T ↦ X`, `E ↦ error` and `Y_(j+1) ↦ (D^(j+1)P)(center + X)` gives a
multiple of `X ^ m` whenever `X ^ d ∣ error`. The divisibility of `error` is needed because `E`
has contact weight `d`. -/
theorem X_pow_dvd_localPolynomialEvaluation_of_lowContact (F : LocalPolynomial R d)
    (hcoeff : ∀ e, localContactOrder d e < m → F.coeff e = 0)
    (center : R) (P error : Polynomial R) (herror : Polynomial.X ^ d ∣ error) :
    Polynomial.X ^ m ∣ localPolynomialEvaluation center P error F := by
  have hF : F ∈ restrictWeightedOrder (R := R) (localContactWeight d) m :=
    mem_restrictWeightedOrder.mpr fun e he ↦
      not_lt.mp fun h ↦ mem_support_iff.mp he (hcoeff e h)
  have hg (v : LocalVariable d) :
      Polynomial.X ^ localContactWeight d v ∣ localPolynomialValues center P error v := by
    rcases v with _ | _ | j
    · simp [localContactWeight, localPolynomialValues]
    · exact herror
    · simp [localContactWeight]
  exact pow_dvd_eval₂Hom_of_mem_restrictWeightedOrder Polynomial.C hF hg

/-- If `Q` satisfies the local constraints of order `m` at `(center, received)` and
`P(center) = received`, then `X ^ m` divides the shifted-jet substitution
`Q(center + X, P(center + X), ..., (DᵈP)(center + X))`. The hypothesis `P(center) = received`
is needed: the constraints only see `P` through the received value at `center`. -/
theorem X_pow_dvd_shiftedJetSubstitution_of_contact (Q : DifferentialPolynomial R d)
    (P : Polynomial R) (center received : R) (hP : P.eval center = received)
    (hQ : SatisfiesLocalConstraints m center received Q) :
    Polynomial.X ^ m ∣ shiftedJetSubstitution center P Q := by
  rw [← localPolynomialEvaluation_unscaled_backwardError Q center received P hP]
  exact X_pow_dvd_localPolynomialEvaluation_of_lowContact _
    ((satisfiesLocalConstraints_iff_coeff_eq_zero m center received Q).mp hQ) center P _
    (Polynomial.X_pow_dvd_normalizedBackwardTaylorError center P d)

/-- Centered form of `X_pow_dvd_shiftedJetSubstitution_of_contact`: the local constraints of order
`m` at `(center, P(center))` force `(X - center) ^ m ∣ Q(X, P, D¹P, ..., DᵈP)`. -/
theorem X_sub_C_pow_dvd_differentialSpecialization_of_contact (Q : DifferentialPolynomial R d)
    (P : Polynomial R) (center received : R) (hP : P.eval center = received)
    (hQ : SatisfiesLocalConstraints m center received Q) :
    (Polynomial.X - Polynomial.C center) ^ m ∣ differentialSpecialization Q P := by
  rw [← Polynomial.X_pow_dvd_taylor_iff_X_sub_C_pow_dvd, taylor_differentialSpecialization]
  exact X_pow_dvd_shiftedJetSubstitution_of_contact Q P center received hP hQ

end ReedSolomon.HiddenDerivative
