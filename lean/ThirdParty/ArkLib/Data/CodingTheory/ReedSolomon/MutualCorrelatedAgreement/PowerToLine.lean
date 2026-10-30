/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerToLine.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
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

import Mathlib.LinearAlgebra.Matrix.Hadamard
import ThirdParty.ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.ExtensionDescent
import ThirdParty.ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement
/-!
# Exact line agreement from degree-one power batching

At batching degree one, exact power agreement for two words is equivalent to an exact
correlated-pair witness. A uniform exact power guarantee therefore supplies the exact-agreement
interface for affine lines.

## Main statements

* `ReedSolomon.exactCorrelatedPair_of_powerAgreement_one`: degree-one exact power agreement gives
  an exact correlated-pair witness.
* `ReedSolomon.powerAgreement_one_of_exactCorrelatedPair`: an exact correlated-pair witness gives
  degree-one exact power agreement.
* `ReedSolomon.powerBatchedWord_pair_eq`: the degree-one power-batched word is the correlated line.
* `ReedSolomon.exists_line_exactCorrelatedPair_of_powerAgreement`: an exceptional set for exact
  degree-one power agreement is an exceptional set for exact correlated-pair agreement.
* `ReedSolomon.lineExactAgreementBound_of_exactCorrelatedPair`,
  `ReedSolomon.lineExactAgreementBound_of_powerAgreement_one`: a uniform exact correlated-pair
  or degree-one power guarantee gives a uniform exact-agreement bound for lines.

## References

* [DKT26]
-/

noncomputable section

open Polynomial

namespace ReedSolomon

variable {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] {n k : ℕ}

omit [DecidableEq F] [DecidableEq E] in
/-- Degree-one power batching of two words is their correlated line. -/
theorem powerBatchedWord_pair_eq (f g : Fin n → F) (ι : F →+* E) (z : E) :
    powerBatchedWord (fun t i ↦ ι (![f, g] t i)) z =
      (fun i ↦ ι (f i) + z * ι (g i)) := by
  funext i
  simp [powerBatchedWord, Fin.sum_univ_two]

/-- Exact power agreement for two constituents is exact correlated-pair agreement. -/
theorem exactCorrelatedPair_of_powerAgreement_one
    (domain : Fin n ↪ F) (w : Fin 2 → Fin n → F) (ι : F →+* E) (z : E) (Q : E[X])
    (h : HasExactPowerAgreement domain w ι k z Q) :
    HasExactCorrelatedPair domain (w 0) (w 1) ι k z Q := by
  obtain ⟨P, hdeg, hQ, hagree⟩ := h
  refine ⟨(P 0, P 1), hdeg 0, hdeg 1, ?_, ?_⟩
  · simpa [powerBatchedPolynomial, correlatedPairSpecialization, Fin.sum_univ_two,
      Polynomial.smul_eq_C_mul] using hQ
  · have hw : powerBatchedWord (fun t i ↦ ι (w t i)) z =
        (fun i ↦ ι (w 0 i) + z * ι (w 1 i)) := by
      have hw : w = ![w 0, w 1] := by
        funext t
        fin_cases t <;> rfl
      rw [hw]
      exact powerBatchedWord_pair_eq (w 0) (w 1) ι z
    rw [hw] at hagree
    simpa [commonCurveAgreementSet, commonPolynomialAgreementSet,
      Fin.forall_fin_two] using hagree

end ReedSolomon
