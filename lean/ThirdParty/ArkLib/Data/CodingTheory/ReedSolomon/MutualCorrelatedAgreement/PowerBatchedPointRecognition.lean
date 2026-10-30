/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedPointRecognition.lean,
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 3 of the 8 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement
import ThirdParty.ArkLib.Data.Polynomial.Differential.TaylorChart
import ThirdParty.ArkLib.ToMathlib.Polynomial.SparseContraction
/-!
# Point recognition for power-batched polynomial graphs

A sample of agreement positions determines a tuple of base-field polynomials. Sparse Frobenius
pullbacks agreeing with the associated power-batched word on the sample are recognized from their
values at roots of the evaluation points. Symbolic Taylor charts also identify the initial jet and
cleared Taylor coefficients of the reconstructed polynomial.

## Main statements

* `commonCurveAgreementSet_map` and `exists_exceptional_powerBatched_extension`: scalar extension
  preserves common agreement positions and transfers the exceptional-challenge bound for any
  finite coordinate type.
* `exists_exceptional_exactPowerAgreement` and `exists_exceptional_exactPowerAgreement_family`:
  exact power agreement outside a bounded exceptional set for a tuple or a finite family.
* `exists_frobeniusPowerGraph_polynomials_of_sample`: a sample recognizes sparse Frobenius
  pullbacks of power-batched polynomial graphs.
* `powerBatchedJetGraph` and `polynomialJet_powerBatched`: initial jets commute with power
  batching.
* `exists_polynomialGraph_of_symbolic_sample_of_exponent`: symbolic Taylor cuts recognize the
  polynomial graph determined by the sample.

## References

* [DKT26]
-/

namespace ReedSolomon

open Polynomial PolynomialDifferential

noncomputable section

variable {F E α : Type*} [Field F] [Field E] {k K r ℓ L : ℕ}

open Classical in
/-- Scalar extension preserves exactly the common agreement positions of a polynomial tuple. -/
theorem commonCurveAgreementSet_map [Fintype α] (domain : α ↪ F)
    (w : Fin (ℓ + 1) → α → F) (P : Fin (ℓ + 1) → F[X]) (iota : F →+* E) :
    commonCurveAgreementSet (domain.trans ⟨iota, iota.injective⟩) (fun t i ↦ iota (w t i))
      (fun t ↦ (P t).map iota) = commonCurveAgreementSet domain w P := by
  classical
  ext i
  simp only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and,
    Function.Embedding.trans_apply, Function.Embedding.coeFn_mk, Polynomial.eval_map,
    Polynomial.eval₂_at_apply, iota.injective.eq_iff]

open Classical in
/-- One exceptional set gives exact power agreement for every tuple in a finite family, with
size at most `family.card * ℓ * (|α| - L)`. -/
theorem exists_exceptional_exactPowerAgreement_family [Fintype α] (domain : α ↪ F)
    (w : Fin (ℓ + 1) → α → F) (iota : F →+* E)
    (family : Finset (Fin (ℓ + 1) → F[X]))
    (hdegree : ∀ P ∈ family, ∀ t, (P t).degree < k)
    (hcommon : ∀ P ∈ family, L ≤ (commonCurveAgreementSet domain w P).card) :
    ∃ exceptional : Finset E,
      exceptional.card ≤ family.card * (ℓ * (Fintype.card α - L)) ∧
      ∀ P ∈ family, ∀ z ∉ exceptional,
        HasExactPowerAgreement domain w iota k z
          (powerBatchedPolynomial (fun t ↦ (P t).map iota) z) := by
  classical
  let domainE := domain.trans ⟨iota, iota.injective⟩
  let wordsE := fun t i ↦ iota (w t i)
  let mapTuple (P : Fin (ℓ + 1) → F[X]) : Fin (ℓ + 1) → E[X] :=
    fun t ↦ (P t).map iota
  let familyE := family.image mapTuple
  have hcommonE : ∀ P ∈ familyE,
      L ≤ (commonCurveAgreementSet domainE wordsE P).card := by
    intro P hP
    obtain ⟨P₀, hP₀, rfl⟩ := Finset.mem_image.mp hP
    rw [commonCurveAgreementSet_map]
    exact hcommon P₀ hP₀
  obtain ⟨ex, hcard, hgood⟩ :=
    exists_exceptional_powerBatched_family domainE wordsE familyE L hcommonE
  refine ⟨ex, hcard.trans (Nat.mul_le_mul_right _ Finset.card_image_le), ?_⟩
  intro P hP z hz
  refine ⟨P, hdegree P hP, rfl, ?_⟩
  have hset := hgood (mapTuple P) (Finset.mem_image.mpr ⟨P, hP, rfl⟩) z hz
  simpa only [domainE, wordsE, familyE, mapTuple] using
    hset.trans (commonCurveAgreementSet_map domain w P iota)

/-- A sample of `k` positions recognizes a sparse Frobenius pullback of the power-batched
polynomial graph. The root and value conditions are needed only on the sample. -/
theorem exists_frobeniusPowerGraph_polynomials_of_sample
    (domain : α ↪ F) (w : Fin (ℓ + 1) → α → F)
    (sample : Finset α) (hsample : sample.card = k) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      (∀ i ∈ sample, ∀ t, (P t).eval (domain i) = w t i) ∧
      ∀ {E : Type*} [Field E] (ι : F →+* E) (p e : ℕ) [ExpChar E p]
        (roots : α → E) (center z : E) (Q : E[X]),
        (∀ i ∈ sample, roots i ^ (p ^ e) = ι (domain i)) →
        Q.degree < ↑(p ^ e * k) →
        (∀ j : ℕ, ¬p ^ e ∣ j → (taylor center Q).coeff j = 0) →
        (∀ i ∈ sample,
          Q.eval (roots i) = ∑ t, z ^ (p ^ e * t.val) * ι (w t i)) →
        Q = expand E (p ^ e)
            (powerBatchedPolynomial (fun t ↦ (P t).map ι) (z ^ (p ^ e))) ∧
          Q.eval center =
            (powerBatchedPolynomial (fun t ↦ (P t).map ι)
              (z ^ (p ^ e))).eval (center ^ (p ^ e)) := by
  obtain ⟨P, hPdegree, hPsample, hrecognize⟩ :=
    exists_polynomialGraph_of_sample domain w sample hsample
  refine ⟨P, hPdegree, hPsample, ?_⟩
  intro E _ ι p e _ roots center z Q hroots hdegree hsparse hagree
  obtain ⟨R, ⟨hRdegree, hRQ⟩, _⟩ :=
    existsUnique_expand_of_sparse_taylor p e k Q center hsparse hdegree
  have hRagree : ∀ i ∈ sample,
      R.eval (domain.trans ⟨ι, ι.injective⟩ i) =
        ∑ t, (z ^ (p ^ e)) ^ t.val * ι (w t i) := by
    intro i hi
    have hiAgree := hagree i hi
    rw [← hRQ, expand_eval, hroots i hi] at hiAgree
    simpa only [Function.Embedding.trans_apply, Function.Embedding.coeFn_mk, pow_mul]
      using hiAgree
  have hRidentity := hrecognize ι (z ^ (p ^ e)) R hRdegree hRagree
  constructor
  · rw [← hRQ, hRidentity]
  · rw [← hRQ, expand_eval, hRidentity]

end

end ReedSolomon
