/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/EquationDescent.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 1 of the 2 declarations of the file is kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ExtensionDescent
import ThirdParty.ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement
import ThirdParty.ArkLib.Data.Polynomial.Differential.BaseChange

/-!
# Descending equation-restricted correlated agreement

Suppose a symbolic differential equation over a field extension has an exceptional set outside
which every close root has an exact correlated-pair witness. Restricting the exceptional set to
the base field preserves its size bound, and roots of the specialized base equation map to roots
of the extension equation. The exact pair then descends to the base field. The same holds for
exact power agreement with a power-batched word.

## Main statements

* `ReedSolomon.exists_exceptional_equation_correlatedAgreement_descend`: equation-restricted
  exact correlated agreement descends with the same exceptional-set bound.
* `ReedSolomon.exists_exceptional_equation_powerAgreement_descend`: equation-restricted exact
  power agreement descends with the same exceptional-set bound.

## References

* [DKT26]
-/

open PolynomialDifferential Polynomial

namespace ReedSolomon

open PolynomialDifferential

variable {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] {n r : ℕ}

/-- A uniform exceptional-set transfer to exact power agreement, for roots of a symbolic
differential equation, descends from an extension field with the same exceptional-set budget. -/
theorem exists_exceptional_equation_powerAgreement_descend {α : Type*} [Fintype α] {ℓ : ℕ}
    (domain : α ↪ F) (values : Fin (ℓ + 1) → α → F) (ι : F →+* E)
    (Q : DifferentialPolynomial F[X] r) (k A : ℕ) (exceptional : Finset E)
    (hgood : ∀ z ∉ exceptional, ∀ P : E[X], P.degree < k →
      A ≤ (polynomialAgreementSet (domain.trans ⟨ι, ι.injective⟩)
        (powerBatchedWord (fun t i ↦ ι (values t i)) z) P).card →
      differentialSpecialization
        (challengeSpecialization (MvPolynomial.map (Polynomial.mapRingHom ι) Q) z) P = 0 →
      HasExactPowerAgreement domain values ι k z P) :
    ∃ baseExceptional : Finset F, baseExceptional.card ≤ exceptional.card ∧
      ∀ z ∉ baseExceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (powerBatchedWord values z) P).card →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        HasExactPowerAgreement domain values (RingHom.id F) k z P := by
  classical
  refine ⟨exceptional.preimage ι ι.injective.injOn,
    Finset.card_le_card_of_injOn ι (fun z hz ↦ Finset.mem_preimage.mp hz) ι.injective.injOn, ?_⟩
  intro z hz P hdegree hagree hroot
  apply HasExactPowerAgreement.descend (φ := ι)
  apply hgood (ι z)
  · exact fun hmem ↦ hz (Finset.mem_preimage.mpr hmem)
  · exact Polynomial.degree_map_le.trans_lt hdegree
  · rwa [powerBatchedWord_map, polynomialAgreementSet_map]
  · rw [← map_symbolicDifferentialSpecialization, hroot, Polynomial.map_zero]

end ReedSolomon
