/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/Polynomial/Differential/RationalTaylorBidegree.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 4 of the 10 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.Data.Polynomial.Differential.TaylorChartAlgebra

/-!
# Capped bidegrees of rational Taylor chart equations

For a differential polynomial over `F[X]`, coefficient degree measures the challenge variable and
total degree in the jet variables measures the initial jet. The flattened initial equation, initial
separant, padded Taylor numerators, and agreement equations therefore lie in bidegree rectangles.

## Main statements

* `initialJetEquation_mem_restrictBidegree` and
  `initialJetSeparant_mem_restrictBidegree`: the initial equation and separant rectangles.
* `initialJetSeparant_mem_restrictCappedBidegree`: a separate highest-jet bound for the
  initial separant at arbitrary differential order.
* `commonTaylorNumeratorOver_mem_restrictBidegree`: the rectangle for a padded Taylor numerator.
* `taylorAgreementEquationOver_mem_restrictBidegree`: the rectangle for an agreement equation
  with a received polynomial of bounded degree.
* `degreeOf_taylorAgreementEquationOver_firstOrder`: a separate degree bound in the first
  derivative variable for an agreement equation.
* `degreeOf_taylorAgreementEquation_firstOrder_le`: its field-valued first-order specialization.
* `initialJetEquation_mem_restrictCappedBidegree`,
  `commonTaylorNumeratorOver_mem_restrictCappedBidegree`, and
  `taylorAgreementEquationOver_mem_restrictCappedBidegree`: the same equations with a separate
  bound on their highest jet variable.

## References

* [DKT26]
-/

namespace PolynomialDifferential

open MvPolynomial Polynomial

variable {F : Type*} [Field F] {r : ℕ}

/-- The flattened initial equation lies in the rectangle given by the coefficient and jet degrees
of `Q`. -/
theorem initialJetEquation_mem_restrictBidegree (center : F)
    (Q : DifferentialPolynomial (Polynomial F) r) (h v : ℕ)
    (hheight : CoeffNatDegreeLE Q h) (hjet : jetTotalDegree Q ≤ v) :
    (optionEquivRight F (Fin (r + 1))).symm
      (initialJetEquation (Polynomial.C center) Q) ∈
        restrictBidegree (Fin (r + 1)) F h v := by
  apply optionEquivRight_symm_mem_restrictBidegree
  · exact coeffNatDegreeLE_initialJetEquation center Q hheight
  · exact (totalDegree_initialJetEquation_le (Polynomial.C center) Q).trans hjet

/-- The flattened initial separant lies in the rectangle with jet bound `v - 1`. -/
theorem initialJetSeparant_mem_restrictBidegree (center : F)
    (Q : DifferentialPolynomial (Polynomial F) r) (h v : ℕ)
    (hheight : CoeffNatDegreeLE Q h) (hjet : jetTotalDegree Q ≤ v) :
    (optionEquivRight F (Fin (r + 1))).symm
      (initialJetSeparant (Polynomial.C center) Q) ∈
        restrictBidegree (Fin (r + 1)) F h (v - 1) := by
  apply optionEquivRight_symm_mem_restrictBidegree
  · exact coeffNatDegreeLE_initialJetSeparant Q center hheight
  · exact (totalDegree_initialJetSeparant_le (Polynomial.C center) Q).trans
      (Nat.sub_le_sub_right hjet 1)

/-- A common Taylor numerator padded to a sufficient exponent lies in its challenge and jet degree
rectangle. -/
theorem commonTaylorNumeratorOver_mem_restrictBidegree (center : F)
    (Q : DifferentialPolynomial (Polynomial F) r) (h v K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hheight : CoeffNatDegreeLE Q h)
    (hv : 0 < v) (hjet : jetTotalDegree Q ≤ v) (l : Fin K) :
    (optionEquivRight F (Fin (r + 1))).symm
      (commonTaylorNumeratorOver F (Polynomial.C center) Q τ l.val) ∈
        restrictBidegree (Fin (r + 1)) F (τ * h) (1 + τ * (v - 1)) := by
  apply optionEquivRight_symm_mem_restrictBidegree
  · exact coeffNatDegreeLE_commonTaylorNumeratorOver_le center Q h τ l.val
      (hτ l) hheight
  · exact totalDegree_commonTaylorNumeratorOver_le_of_jet_and_exponent
      (Polynomial.C center) Q v K τ hv hτ hjet l

/-- Agreement with a received polynomial of degree at most `ell`, padded to a sufficient exponent,
lies in the corresponding bidegree rectangle. -/
theorem taylorAgreementEquationOver_mem_restrictBidegree (center x : F) (y : Polynomial F)
    (Q : DifferentialPolynomial (Polynomial F) r) (ell h v K τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hy : y.natDegree ≤ ell)
    (hheight : CoeffNatDegreeLE Q h) (hv : 0 < v) (hjet : jetTotalDegree Q ≤ v) :
    (optionEquivRight F (Fin (r + 1))).symm
      (taylorAgreementEquationOver (F := F) (A := Polynomial F)
        (Polynomial.C center) Q K (Polynomial.C x) y (τ := τ)) ∈
        restrictBidegree (Fin (r + 1)) F (ell + τ * h) (1 + τ * (v - 1)) := by
  apply optionEquivRight_symm_mem_restrictBidegree
  · unfold taylorAgreementEquationOver
    rw [sub_eq_add_neg]
    apply CoeffNatDegreeLE.add
    · apply coeffNatDegreeLE_sum
      intro l _
      apply (coeffNatDegreeLE_C (by simp)).mul
      exact (coeffNatDegreeLE_commonTaylorNumeratorOver_le center Q h τ l.val
        (hτ l) hheight).mono (by omega)
    · intro m
      simpa using (((coeffNatDegreeLE_C hy).mul
        ((coeffNatDegreeLE_initialJetSeparant Q center hheight).pow τ)) m)
  · unfold taylorAgreementEquationOver
    apply (totalDegree_sub _ _).trans
    apply max_le
    · apply totalDegree_finsetSum_le
      intro l _
      apply (totalDegree_mul _ _).trans
      simpa only [totalDegree_C, zero_add] using
        totalDegree_commonTaylorNumeratorOver_le_of_jet_and_exponent
          (Polynomial.C center) Q v K τ hv hτ hjet l
    · apply (totalDegree_mul _ _).trans
      simp only [totalDegree_C, zero_add]
      have hs := (totalDegree_pow
          (initialJetSeparant (Polynomial.C center) Q) τ).trans
        (Nat.mul_le_mul_left τ
          ((totalDegree_initialJetSeparant_le (Polynomial.C center) Q).trans
            (Nat.sub_le_sub_right hjet 1)))
      exact hs.trans (by omega)

end PolynomialDifferential
