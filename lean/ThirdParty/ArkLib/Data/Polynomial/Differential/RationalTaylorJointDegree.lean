/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/Polynomial/Differential/RationalTaylorJointDegree.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 8 of the 14 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.Data.Polynomial.Differential.RationalTaylorAlgebra

/-!
# Degree bounds for rational Taylor numerators with a polynomial parameter

Let `Q` be a differential polynomial with coefficients in `F[X]`, where the variable `X` is a
parameter. The rational Taylor numerators of `Q`, computed over the `F`-algebra `F[X]` by
`rationalTaylorNumeratorOver`, are polynomials in the initial jet with coefficients in `F[X]`.
This file bounds their `MvPolynomial.jointTotalDegree`, the total degree in the jet coordinates
and the parameter together. It also bounds coefficient degree in the parameter and total degree
in the jet variables separately.

Taylor substitution at a constant center `C c` does not raise the degree in the parameter: if
every coefficient of `Q` has degree at most `h` in `X`, so does every coefficient of the initial
separant and of the universal residual (`MvPolynomial.CoeffNatDegreeLE`). If moreover `Q` has
total jet degree at most `v`, the numerator of `c_l` has joint degree at most
`(2(l - r) - 1) * (v - 1 + h) + 1`, linear in the order `l`. Padding to an exponent
`τ ≥ 2(l - r) - 1` gives the bound `1 + τ * (v - 1 + h)`, which does not depend on `l`.

## Main statements

* `coeffNatDegreeLE_initialJetSeparant`, `coeffNatDegreeLE_universalTaylorJet`,
  `coeffNatDegreeLE_universalTaylorResidual`, and
  `coeffNatDegreeLE_universalTaylorResidual_coeff`: at a constant center, the parameter degree
  of `Q` bounds that of the separant and of the residual.
* `jointTotalDegree_initialJetSeparant_le`: the separant has joint degree at most `v - 1 + h`.
* `jointTotalDegree_rationalTaylorNumeratorOver_le`: the recursion bound, from a bound `b` on
  the separant and `b + 1` on the residual coefficients.
* `jointTotalDegree_rationalTaylorNumeratorOver_le_of_coeffNatDegreeLE`: the bound
  `(2(l - r) - 1) * (v - 1 + h) + 1` at a constant center.
* `jointTotalDegree_commonTaylorNumeratorOver_le` and
  `jointTotalDegree_commonTaylorNumeratorOver_le_of_coeffNatDegreeLE`: the common-exponent
  bounds `1 + τ * b` and `1 + τ * (v - 1 + h)`.
* `coeffNatDegreeLE_rationalTaylorNumeratorOver` and
  `coeffNatDegreeLE_commonTaylorNumeratorOver_le`: coefficient-degree bounds for the same
  numerators.
* `totalDegree_rationalTaylorNumeratorOver_le_of_jet` and
  `totalDegree_commonTaylorNumeratorOver_le_of_jet_and_exponent`: bounds on degree in the jet
  variables alone.

## References

* [DKT26]
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial

/-! ### Parameter degree under Taylor substitution -/

section CommSemiring

variable {R : Type*} [CommSemiring R] {r h : ℕ}

/-- At a constant center, the initial separant has coefficient degree at most `h` in the
parameter when `Q` does. -/
theorem coeffNatDegreeLE_initialJetSeparant (Q : DifferentialPolynomial (Polynomial R) r)
    (c : R) (hQ : CoeffNatDegreeLE Q h) :
    CoeffNatDegreeLE (initialJetSeparant (Polynomial.C c) Q) h := by
  apply (hQ.pderiv (some (Fin.last r))).aeval
  intro i
  cases i with
  | none => exact coeffNatDegreeLE_C (by simp)
  | some i => exact coeffNatDegreeLE_X i

/-- The universal Taylor jet has constant coefficients. -/
theorem coeffNatDegreeLE_universalTaylorJet (K j : ℕ) :
    CoeffNatDegreeLE (universalTaylorJet (F := Polynomial R) K j) 0 := by
  rw [← map_universalTaylorJet (Polynomial.C : R →+* Polynomial R)]
  exact coeffNatDegreeLE_map_C _

/-- At a constant center, the universal residual has coefficient degree at most `h` in the
parameter when `Q` does. -/
theorem coeffNatDegreeLE_universalTaylorResidual (Q : DifferentialPolynomial (Polynomial R) r)
    (c : R) (hQ : CoeffNatDegreeLE Q h) (K : ℕ) :
    CoeffNatDegreeLE (universalTaylorResidual K (Polynomial.C c) Q) h := by
  apply hQ.aeval
  intro i
  cases i with
  | none => exact (coeffNatDegreeLE_C (by simp)).add (coeffNatDegreeLE_X none)
  | some j => exact coeffNatDegreeLE_universalTaylorJet K j.val

/-- At a constant center, every displacement coefficient of the universal residual has
coefficient degree at most `h` in the parameter when `Q` does. -/
theorem coeffNatDegreeLE_universalTaylorResidual_coeff
    (Q : DifferentialPolynomial (Polynomial R) r) (c : R) (hQ : CoeffNatDegreeLE Q h)
    (K t : ℕ) :
    CoeffNatDegreeLE ((optionEquivLeft (Polynomial R) (Fin K)
      (universalTaylorResidual K (Polynomial.C c) Q)).coeff t) h := by
  intro m
  rw [optionEquivLeft_coeff_coeff]
  exact coeffNatDegreeLE_universalTaylorResidual Q c hQ K _

end CommSemiring

/-! ### Joint degree of the numerators -/

variable {F : Type*} [Field F] {r : ℕ}

/-! ### Separate coefficient and jet degree bounds -/

section SeparateDegrees

variable {F : Type*} [Field F] {r : ℕ}

/-- The coefficient degree of the rational Taylor numerator is at most
`(2(l - r) - 1) * h` when each coefficient of `Q` has degree at most `h` in the parameter. -/
theorem coeffNatDegreeLE_rationalTaylorNumeratorOver (center : F)
    (Q : DifferentialPolynomial (Polynomial F) r) (h : ℕ)
    (hQ : CoeffNatDegreeLE Q h) (l : ℕ) :
    CoeffNatDegreeLE (rationalTaylorNumeratorOver F (Polynomial.C center) Q l)
      ((2 * (l - r) - 1) * h) := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
    rw [rationalTaylorNumeratorOver]
    split_ifs with hl
    · exact (coeffNatDegreeLE_X _).mono (Nat.zero_le _)
    · have hh : 0 < l - r := by omega
      have hden := denominator_weight_le_of_mem_universalTaylorResidual_coeff
        (r := r) (h := l - r) (by omega : l ≤ r + (l - r))
        (Polynomial.C center) Q
      have hd := CoeffNatDegreeLE.clearedSubstitution
        (initialJetSeparant (Polynomial.C center) Q)
        (fun i : Fin l ↦ rationalTaylorNumeratorOver F (Polynomial.C center) Q i.val)
        (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2) h h
        ((optionEquivLeft (Polynomial F) (Fin l)
          (universalTaylorResidual l (Polynomial.C center) Q)).coeff (l - r))
        (coeffNatDegreeLE_initialJetSeparant Q center hQ)
        (fun i ↦ ih i.val i.isLt) hden
        (fun m _ ↦ coeffNatDegreeLE_universalTaylorResidual_coeff Q center hQ
          l (l - r) m)
      have hc : CoeffNatDegreeLE
          (-MvPolynomial.C (algebraMap F (Polynomial F) ((l.choose r : F)⁻¹)) :
            MvPolynomial (Fin (r + 1)) (Polynomial F)) 0 := by
        intro m
        rw [coeff_neg, coeff_C]
        split_ifs <;> simp
      have hm := hc.mul hd
      have he : 2 * (l - r) - 1 = (2 * (l - r) - 2) + 1 := by omega
      rw [he]
      simpa only [Polynomial.algebraMap_eq, zero_add, add_mul, one_mul] using hm

/-- The numerator padded to exponent `τ` has coefficient degree at most `τ * h` whenever the
exponent covers its denominator. -/
theorem coeffNatDegreeLE_commonTaylorNumeratorOver_le (center : F)
    (Q : DifferentialPolynomial (Polynomial F) r) (h τ l : ℕ)
    (hτ : 2 * (l - r) - 1 ≤ τ) (hQ : CoeffNatDegreeLE Q h) :
    CoeffNatDegreeLE (commonTaylorNumeratorOver F (Polynomial.C center) Q τ l) (τ * h) := by
  unfold commonTaylorNumeratorOver
  have hn := coeffNatDegreeLE_rationalTaylorNumeratorOver center Q h hQ l
  have hs := (coeffNatDegreeLE_initialJetSeparant Q center hQ).pow
    (τ - (2 * (l - r) - 1))
  have hm := hn.mul hs
  apply hm.mono
  rw [← Nat.add_mul, Nat.add_sub_of_le hτ]

/-- The rational Taylor numerator has total degree at most
`(2(l - r) - 1) * (v - 1) + 1` in the jet variables. -/
theorem totalDegree_rationalTaylorNumeratorOver_le_of_jet (center : Polynomial F)
    (Q : DifferentialPolynomial (Polynomial F) r) (v : ℕ)
    (hv : 0 < v) (hjet : jetTotalDegree Q ≤ v) (l : ℕ) :
    (rationalTaylorNumeratorOver F center Q l).totalDegree ≤
      (2 * (l - r) - 1) * (v - 1) + 1 := by
  induction l using Nat.strong_induction_on with
  | h l ih =>
    rw [rationalTaylorNumeratorOver]
    split_ifs with hl
    · simp only [totalDegree_X]
      omega
    · have hh : 0 < l - r := by omega
      have hden := denominator_weight_le_of_mem_universalTaylorResidual_coeff
        (r := r) (h := l - r) (by omega : l ≤ r + (l - r)) center Q
      have hd := totalDegree_clearedSubstitution
        (initialJetSeparant center Q)
        (fun i : Fin l ↦ rationalTaylorNumeratorOver F center Q i.val)
        (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2) (v - 1) v
        ((optionEquivLeft (Polynomial F) (Fin l)
          (universalTaylorResidual l center Q)).coeff (l - r))
        ((totalDegree_initialJetSeparant_le center Q).trans
          (Nat.sub_le_sub_right hjet 1))
        (fun i ↦ ih i.val i.isLt) hden
        ((totalDegree_universalTaylorResidual_coeff_le l center Q (l - r)).trans hjet)
      have hm := totalDegree_mul
        (-MvPolynomial.C (algebraMap F (Polynomial F) ((l.choose r : F)⁻¹)) :
          MvPolynomial (Fin (r + 1)) (Polynomial F))
        (clearedSubstitution C (initialJetSeparant center Q)
          (fun i : Fin l ↦ rationalTaylorNumeratorOver F center Q i.val)
          (fun i ↦ 2 * (i.val - r) - 1) (2 * (l - r) - 2)
          ((optionEquivLeft (Polynomial F) (Fin l)
            (universalTaylorResidual l center Q)).coeff (l - r)))
      simp only [totalDegree_neg, totalDegree_C, zero_add] at hm
      have he : 2 * (l - r) - 1 = (2 * (l - r) - 2) + 1 := by omega
      rw [he]
      have hbound := hm.trans hd
      have hvsub := Nat.sub_add_cancel (Nat.succ_le_of_lt hv)
      nlinarith [hbound, hvsub]

/-- For a sufficient exponent, the common Taylor numerator has total degree at most
`1 + τ * (v - 1)` in the jet variables. -/
theorem totalDegree_commonTaylorNumeratorOver_le_of_jet_and_exponent
    (center : Polynomial F) (Q : DifferentialPolynomial (Polynomial F) r)
    (v K τ : ℕ) (hv : 0 < v) (hτ : TaylorExponentSufficient r K τ)
    (hjet : jetTotalDegree Q ≤ v) (l : Fin K) :
    (commonTaylorNumeratorOver F center Q τ l.val).totalDegree ≤ 1 + τ * (v - 1) := by
  have hd := totalDegree_rationalTaylorNumeratorOver_le_of_jet center Q v hv hjet l.val
  have hs := (totalDegree_initialJetSeparant_le center Q).trans
    (Nat.sub_le_sub_right hjet 1)
  have hp := (totalDegree_pow (initialJetSeparant center Q)
    (τ - (2 * (l.val - r) - 1))).trans (Nat.mul_le_mul_left _ hs)
  have hm := totalDegree_mul (rationalTaylorNumeratorOver F center Q l.val)
    (initialJetSeparant center Q ^ (τ - (2 * (l.val - r) - 1)))
  have he := Nat.sub_add_cancel (hτ l)
  unfold commonTaylorNumeratorOver
  nlinarith

end SeparateDegrees

end

end PolynomialDifferential
