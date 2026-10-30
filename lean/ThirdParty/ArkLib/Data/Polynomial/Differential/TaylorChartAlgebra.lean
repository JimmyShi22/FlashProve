/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/Polynomial/Differential/TaylorChartAlgebra.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 17 of the 24 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.Data.Polynomial.Differential.RationalTaylorJointDegree
import ThirdParty.ArkLib.Data.Polynomial.Differential.TaylorChart

/-!
# Symbolic equations on the rational Taylor chart

The initial equation and separant specialize along coefficient maps. Agreement equations can
also be formed over an algebra, then mapped to a field where they describe the reconstructed
polynomial. Vanishing symbolic high cuts bounds the degree of that reconstruction, and each
symbolic common numerator evaluates to its corresponding Taylor coefficient after clearing the
separant denominator.

## Main statements

* `map_initialJetEquation` and `aeval_map_initialJetEquation` describe coefficient maps and
  evaluation of the initial equation.
* `taylorAgreementEquationOver` and its map theorem define symbolic agreement equations over an
  algebra and specialize them to field-valued cuts.
* `jointInitialJetEquation`, `jointInitialJetSeparant`, and `jointCommonTaylorNumerator` define
  flattened challenge and jet coordinates for the Taylor chart.
* `jointTaylorAgreementEquation`, `jointTaylorReconstructionError`, and `affinePairCurve` describe
  the agreement cuts and affine-pair graph in those coordinates.
* `aeval_jointInitialJetEquation`, `aeval_jointInitialJetSeparant`,
  `aeval_jointCommonTaylorNumerator`, and `aeval_jointTaylorAgreementEquation` specialize joint
  cuts at a point before evaluating jets.
* `jointInitialJetEquation_ne_zero_of_regular` certifies the joint initial equation from a regular
  specialized jet.
* `commonTaylorNumeratorOver_eq` and `map_commonTaylorNumeratorOver_eq` bridge algebra-valued
  numerators to their field-valued counterparts.
* `aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent` characterizes regular agreement
  cuts, while `degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts_and_exponent` bounds the
  reconstruction degree.
* `aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent` identifies symbolic common
  numerators with coefficients of the reconstructed polynomial.
* `jointTotalDegree_initialJetEquation_le_of_coeffNatDegreeLE` and
  `jointTotalDegree_taylorAgreementEquationOver_le_of_coeffNatDegreeLE_and_exponent` bound
  symbolic equation degrees from jet degree and coefficient height.
* `sparse_rationalTaylorPolynomial_of_symbolic_cuts` derives coefficient sparsity from symbolic
  cuts at a regular jet.

## References

* [DKT26]
-/

namespace PolynomialDifferential

noncomputable section

open MvPolynomial
open scoped BigOperators

variable {A B : Type*} [CommSemiring A] [CommSemiring B] {r : ℕ}

variable {F : Type*} [Field F] {A B : Type*} [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B]

/-- The coefficient height of `Q` also bounds that of its initial equation at a constant center.
-/
theorem coeffNatDegreeLE_initialJetEquation (center : F)
    (Q : DifferentialPolynomial (Polynomial F) r) {h : ℕ}
    (hQ : CoeffNatDegreeLE Q h) :
    CoeffNatDegreeLE (initialJetEquation (Polynomial.C center) Q) h := by
  apply hQ.aeval
  intro i
  cases i with
  | none => exact coeffNatDegreeLE_C (by simp)
  | some i => exact coeffNatDegreeLE_X i

/-- The agreement equation over an `F`-algebra, with every common numerator using the same
separant exponent. -/
def taylorAgreementEquationOver (center : A) (Q : DifferentialPolynomial A r) (K : ℕ)
    (x y : A) (τ : ℕ) : MvPolynomial (Fin (r + 1)) A :=
  (∑ l : Fin K, C ((x - center) ^ l.val) *
    commonTaylorNumeratorOver F center Q τ l.val) - C y * initialJetSeparant center Q ^ τ

/-- Coefficient specialization maps an algebra-valued agreement equation to the corresponding
agreement equation. -/
theorem map_taylorAgreementEquationOver (φ : A →ₐ[F] B) (center : A)
    (Q : DifferentialPolynomial A r) (K : ℕ) (x y : A) (τ : ℕ) :
    map φ.toRingHom (taylorAgreementEquationOver (F := F) center Q K x y (τ := τ)) =
      taylorAgreementEquationOver (F := F) (φ center) (map φ.toRingHom Q) K
        (φ x) (φ y) (τ := τ) := by
  simp only [taylorAgreementEquationOver, map_sub, map_sum, map_mul, map_C, map_pow,
    map_commonTaylorNumeratorOver, map_initialJetSeparant]
  rfl

/-- Specializing an algebra-valued agreement equation to a field gives the field-valued cut. -/
theorem map_taylorAgreementEquationOver_eq {E : Type*} [Field E] [Algebra F E]
    (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r) (K : ℕ) (x y : A)
    (τ : ℕ) :
    map φ.toRingHom (taylorAgreementEquationOver (F := F) center Q K x y (τ := τ)) =
      taylorAgreementEquation (φ center) (map φ.toRingHom Q) K τ (φ x) (φ y) := by
  rw [map_taylorAgreementEquationOver (τ := τ)]
  simp only [taylorAgreementEquationOver, taylorAgreementEquation,
    commonTaylorNumeratorOver_eq]

/-- The initial equation in joint challenge and initial-jet coordinates. -/
def jointInitialJetEquation {E : Type*} [CommSemiring E] (center : E)
    (Q : DifferentialPolynomial (Polynomial E) r) :
    MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E (Fin (r + 1))).symm
    (initialJetEquation (Polynomial.C center) Q)

/-- The initial separant in joint challenge and initial-jet coordinates. -/
def jointInitialJetSeparant {E : Type*} [CommSemiring E] (center : E)
    (Q : DifferentialPolynomial (Polynomial E) r) :
    MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E (Fin (r + 1))).symm
    (initialJetSeparant (Polynomial.C center) Q)

/-- A cleared Taylor coefficient in joint challenge and initial-jet coordinates. -/
def jointCommonTaylorNumerator {E : Type*} [Field E] (center : E)
    (Q : DifferentialPolynomial (Polynomial E) r)
    (τ : ℕ) {K : ℕ} (l : Fin K) : MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E (Fin (r + 1))).symm
    (commonTaylorNumeratorOver E (Polynomial.C center) Q τ l.val)

/-- The cleared agreement equation in joint challenge and initial-jet coordinates. -/
def jointTaylorAgreementEquation {E : Type*} [Field E] (center : E)
    (Q : DifferentialPolynomial (Polynomial E) r)
    (K τ : ℕ) (x y : Polynomial E) : MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E (Fin (r + 1))).symm
    (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K x y (τ := τ))

variable {E : Type*} [Field E]

/-- A regular specialized jet implies that the joint initial equation is nonzero. -/
theorem jointInitialJetEquation_ne_zero_of_regular (center z : E)
    (Q : DifferentialPolynomial (Polynomial E) r) (jet : Fin (r + 1) → E)
    (hS : aeval jet (initialJetSeparant center
      (MvPolynomial.map (Polynomial.evalRingHom z) Q)) ≠ 0) :
    jointInitialJetEquation center Q ≠ 0 := by
  have hsep : initialJetSeparant center
      (MvPolynomial.map (Polynomial.evalRingHom z) Q) ≠ 0 := by
    intro hzero
    exact hS (by rw [hzero]; simp)
  have hinit := initialJetEquation_ne_zero_of_initialJetSeparant_ne_zero center _ hsep
  intro hzero
  have he : initialJetEquation (Polynomial.C center) Q = 0 := by
    apply (optionEquivRight E (Fin (r + 1))).symm.injective
    simpa only [jointInitialJetEquation, map_zero] using hzero
  have hm := congrArg (MvPolynomial.map (Polynomial.evalRingHom z)) he
  rw [map_initialJetEquation, map_zero,
    show (Polynomial.evalRingHom z) (Polynomial.C center) = center from Polynomial.eval_C] at hm
  exact hinit hm

/-- Evaluating the joint separant specializes its challenge before evaluating the jet. -/
theorem aeval_jointInitialJetSeparant (center : E)
    (Q : DifferentialPolynomial (Polynomial E) r) (x : Option (Fin (r + 1)) → E) :
    aeval x (jointInitialJetSeparant center Q) =
      aeval (fun j ↦ x (some j))
        (initialJetSeparant center
          (MvPolynomial.map (Polynomial.aeval (x none)).toRingHom Q)) := by
  rw [jointInitialJetSeparant, aeval_optionEquivRight_symm, map_initialJetSeparant]
  simp

/-- Evaluating a joint high cut specializes its challenge before evaluating the jet. -/
theorem aeval_jointCommonTaylorNumerator (center : E)
    (Q : DifferentialPolynomial (Polynomial E) r) (τ : ℕ) {K : ℕ} (l : Fin K)
    (x : Option (Fin (r + 1)) → E) :
    aeval x (jointCommonTaylorNumerator center Q τ l) =
      aeval (fun j ↦ x (some j))
        (commonTaylorNumerator center
          (MvPolynomial.map (Polynomial.aeval (x none)).toRingHom Q) τ l.val) := by
  rw [jointCommonTaylorNumerator, aeval_optionEquivRight_symm,
    map_commonTaylorNumeratorOver]
  simp [commonTaylorNumerator, commonTaylorNumeratorOver, rationalTaylorNumeratorOver_eq]

/-- Evaluating a joint agreement cut specializes its challenge and received value. -/
theorem aeval_jointTaylorAgreementEquation (center : E)
    (Q : DifferentialPolynomial (Polynomial E) r) (K τ : ℕ) (x₀ y₀ : Polynomial E)
    (x : Option (Fin (r + 1)) → E) :
    aeval x (jointTaylorAgreementEquation center Q K τ x₀ y₀) =
      aeval (fun j ↦ x (some j))
        (taylorAgreementEquation center
          (MvPolynomial.map (Polynomial.aeval (x none)).toRingHom Q) K τ
          (Polynomial.eval (x none) x₀) (Polynomial.eval (x none) y₀)) := by
  rw [jointTaylorAgreementEquation, aeval_optionEquivRight_symm,
    map_taylorAgreementEquationOver_eq (τ := τ)]
  simp

/-- At a regular jet, a sufficiently padded symbolic agreement equation evaluates to the
separant power times the discrepancy of the reconstructed polynomial. -/
theorem aeval_map_taylorAgreementEquationOver_of_exponent {E : Type*} [Field E]
    [Algebra F E] (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r)
    (K τ : ℕ) (hτ : TaylorExponentSufficient r K τ) (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0) (x y : A) :
    aeval jet (map φ.toRingHom
      (taylorAgreementEquationOver (F := F) center Q K x y (τ := τ))) =
        aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ^ τ *
          ((rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet).eval (φ x) -
            φ y) := by
  rw [map_initialJetSeparant φ.toRingHom center Q] at hS ⊢
  rw [map_taylorAgreementEquationOver_eq (τ := τ)]
  simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using
    aeval_taylorAgreementEquation (φ center) (map φ.toRingHom Q) hτ jet hS (φ x) (φ y)

/-- A regular symbolic agreement equation vanishes exactly when the reconstructed polynomial
takes the received value. -/
theorem aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent {E : Type*}
    [Field E] [Algebra F E] (φ : A →ₐ[F] E) (center : A)
    (Q : DifferentialPolynomial A r) (K τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0) (x y : A) :
    aeval jet (map φ.toRingHom
      (taylorAgreementEquationOver (F := F) center Q K x y (τ := τ))) = 0 ↔
      (rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet).eval (φ x) = φ y := by
  rw [aeval_map_taylorAgreementEquationOver_of_exponent φ center Q K τ hτ jet hS]
  simp only [mul_eq_zero, pow_ne_zero _ hS, false_or, sub_eq_zero]

/-- Vanishing symbolic high cuts with a sufficient exponent bounds the degree of the
reconstructed polynomial. -/
theorem degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts_and_exponent {E : Type*}
    [Field E] [Algebra F E] (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r)
    (K k τ : ℕ) (hτ : TaylorExponentSufficient r K τ) (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      aeval jet (map φ.toRingHom (commonTaylorNumeratorOver F center Q τ l.val)) = 0) :
    (rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet).degree < k := by
  rw [map_initialJetSeparant φ.toRingHom center Q] at hS
  refine degree_rationalTaylorPolynomial_lt (φ center) (map φ.toRingHom Q) hτ k jet hS ?_
  intro l hkl hlK
  simpa only [map_commonTaylorNumeratorOver_eq] using hhigh ⟨l, hlK⟩ hkl

/-- Every symbolic common numerator evaluates to the cleared Taylor coefficient of the
reconstructed polynomial when its exponent is sufficient. -/
theorem aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent {E : Type*}
    [Field E] [Algebra F E] (φ : A →ₐ[F] E) (center : A)
    (Q : DifferentialPolynomial A r) (K τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0) (l : Fin K) :
    aeval jet (map φ.toRingHom
      (commonTaylorNumeratorOver F center Q τ l.val)) =
      aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ^ τ *
        (Polynomial.taylor (φ center)
          (rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet)).coeff l.val := by
  rw [map_initialJetSeparant φ.toRingHom center Q] at hS ⊢
  have hS' : aeval jet (initialJetSeparant (φ center) (map φ.toRingHom Q)) ≠ 0 := by
    simpa only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hS
  rw [map_commonTaylorNumeratorOver_eq,
    aeval_commonTaylorNumerator (φ center) (map φ.toRingHom Q) jet (hτ l) hS']
  rw [rationalTaylorPolynomial, Polynomial.coeff_taylor_centeredCoefficientPrefix]
  simp [l.isLt]

/-- Vanishing symbolic common numerators outside multiples of `s` force the corresponding
Taylor coefficients of the reconstructed polynomial to vanish at a regular jet. -/
theorem sparse_rationalTaylorPolynomial_of_symbolic_cuts {E : Type*} [Field E]
    [Algebra F E] (φ : A →ₐ[F] E) (center : A) (Q : DifferentialPolynomial A r)
    (K s τ : ℕ) (hτ : TaylorExponentSufficient r K τ) (jet : Fin (r + 1) → E)
    (hS : aeval jet (map φ.toRingHom (initialJetSeparant center Q)) ≠ 0)
    (hcuts : ∀ l : Fin K, ¬s ∣ l.val →
      aeval jet (map φ.toRingHom (commonTaylorNumeratorOver F center Q τ l.val)) = 0) :
    ∀ i : ℕ, ¬s ∣ i →
      (Polynomial.taylor (φ center)
        (rationalTaylorPolynomial (φ center) (map φ.toRingHom Q) K jet)).coeff i = 0 := by
  intro i hi
  by_cases hiK : i < K
  · have hnum := hcuts ⟨i, hiK⟩ hi
    have hbridge := aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent
      φ center Q K τ hτ jet hS ⟨i, hiK⟩
    rw [hbridge] at hnum
    exact (mul_eq_zero.mp hnum).resolve_left (pow_ne_zero _ hS)
  · simp [rationalTaylorPolynomial, Polynomial.coeff_taylor_centeredCoefficientPrefix, hiK]

end

end PolynomialDifferential
