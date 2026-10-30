/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/Polynomial/Differential/FrobeniusTaylorWitness.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* The one declaration of the file is kept. ArkLib's comment at the top of the file is unchanged.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.Data.Polynomial.Differential.BaseChange
import ThirdParty.ArkLib.Data.Polynomial.Differential.TaylorChartAlgebra
import ThirdParty.ArkLib.ToMathlib.Polynomial.FrobeniusTaylor

/-!
# Taylor equations of a Frobenius-expanded solution

An expanded solution of a specialized differential equation satisfies the joint Taylor-chart
equations. Its cleared agreement cuts compare a Frobenius-pulled solution value against an
arbitrary polynomial curve at the challenge.

## Main statements

* `PolynomialDifferential.frobeniusExpansion_satisfies_jointTaylorCuts`: chart equations and
  agreement characterization for an expanded solution and any polynomial-valued curve.

## References

* [DKT26]
-/

open Polynomial MvPolynomial

namespace PolynomialDifferential

noncomputable section

/-- The joint Taylor chart of an expanded solution satisfies the initial, regularity, and sparse
equations, and its agreement cuts characterize arbitrary polynomial-valued curves. -/
theorem frobeniusExpansion_satisfies_jointTaylorCuts {E : Type*} [Field E]
    (Q : DifferentialPolynomial E[X] 0) (center w : E) (P : E[X])
    (p e K τ : ℕ) [ExpChar E p]
    (hτ : TaylorExponentSufficient 0 K τ)
    (hdegree : (expand E (p ^ e) P).degree < K)
    (hsol : differentialSpecialization (challengeSpecialization Q w)
      (expand E (p ^ e) P) = 0)
    (hsep : aeval (polynomialJet center (expand E (p ^ e) P))
      (initialJetSeparant center (challengeSpecialization Q w)) ≠ 0) :
    let point : Option (Fin 1) → E := fun i ↦
      i.elim w fun j ↦ polynomialJet center (expand E (p ^ e) P) j
    aeval point (jointInitialJetEquation center Q) = 0 ∧
    aeval point (jointInitialJetSeparant center Q) ≠ 0 ∧
    (∀ l : Fin K, ¬p ^ e ∣ l.val →
      aeval point (jointCommonTaylorNumerator center Q τ l) = 0) ∧
    ∀ alpha : E, ∀ curve : E[X],
      aeval point (jointTaylorAgreementEquation center Q K τ (Polynomial.C alpha)
        curve) = 0 ↔ P.eval (alpha ^ (p ^ e)) = curve.eval w := by
  classical
  let P' := expand E (p ^ e) P
  let jet : Fin 1 → E := polynomialJet center P'
  let point : Option (Fin 1) → E := fun i ↦ i.elim w fun j ↦ jet j
  have hS : aeval jet (initialJetSeparant center (challengeSpecialization Q w)) ≠ 0 := by
    exact hsep
  have hsepJet :
      jetEvaluation (separant (challengeSpecialization Q w) (Fin.last 0)) center jet ≠ 0 := by
    rwa [← aeval_initialJetSeparant]
  have hrec : rationalTaylorPolynomial center (challengeSpecialization Q w) K jet = P' :=
    rationalTaylorPolynomial_polynomialJet center (challengeSpecialization Q w) P' hsol hsepJet
      hdegree (by simp)
  have hcenter : (Polynomial.aeval w).toRingHom (Polynomial.C center) = center := by simp
  have hinitial : aeval point (jointInitialJetEquation center Q) = 0 := by
    rw [jointInitialJetEquation, aeval_optionEquivRight_symm, map_initialJetEquation]
    simpa only [point, jet, P', challengeSpecialization, Option.elim_none, Option.elim_some,
      hcenter] using
      aeval_initialJetEquation_polynomialJet center (challengeSpecialization Q w) P' hsol
  have hregular : aeval point (jointInitialJetSeparant center Q) ≠ 0 := by
    rw [aeval_jointInitialJetSeparant]
    change aeval jet (initialJetSeparant center (challengeSpecialization Q w)) ≠ 0
    exact hS
  have hsparse : ∀ l : Fin K, ¬p ^ e ∣ l.val →
      aeval point (jointCommonTaylorNumerator center Q τ l) = 0 := by
    intro l hl
    rw [aeval_jointCommonTaylorNumerator]
    simp only [point, Option.elim_none, Option.elim_some]
    change aeval jet
      (commonTaylorNumerator center (challengeSpecialization Q w) τ l.val) = 0
    rw [aeval_commonTaylorNumerator center (challengeSpecialization Q w) jet (hτ l) hS]
    rw [rationalTaylorCoefficient_eq_solution center (challengeSpecialization Q w) P' hsol
      hsepJet l.val (by simp), Polynomial.coeff_taylor_expand_expChar_pow_eq_zero p e P center hl]
    simp
  refine ⟨?_, hregular, hsparse, ?_⟩
  · exact hinitial
  · intro alpha curve
    rw [aeval_jointTaylorAgreementEquation]
    simp only [Option.elim_none, Option.elim_some, Polynomial.eval_C]
    change (aeval jet
      (taylorAgreementEquation center (challengeSpecialization Q w) K τ alpha
        (curve.eval w)) = 0) ↔ P.eval (alpha ^ (p ^ e)) = curve.eval w
    have hpoint := taylorAgreementEquation_eq_zero_iff center
      (challengeSpecialization Q w) hτ jet hS alpha (curve.eval w)
    rw [hpoint, hrec]
    simp [P', expand_eval]

end

end PolynomialDifferential
