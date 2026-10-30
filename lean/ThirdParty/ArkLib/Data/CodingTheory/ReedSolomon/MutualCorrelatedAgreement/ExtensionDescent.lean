/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/ExtensionDescent.lean, commit
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

import ThirdParty.ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Pairs.Family

/-!
# Exact correlated-pair witnesses under field extensions

An exact correlated-pair witness consists of two base-field message polynomials whose affine
specialization is a given candidate and whose full common agreement set is the candidate's
agreement set. Injectivity of a field homomorphism lets this witness descend from an extension.

## Main definitions

* `ReedSolomon.HasExactCorrelatedPair`: an exact witness for a challenge and candidate polynomial.

## Main statements

* `ReedSolomon.HasExactCorrelatedPair.descend`: exact witnesses descend to the base field.

## References

* [DKT26]
-/

namespace ReedSolomon

open Polynomial

variable {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E] {n : ℕ}

/-- A pair of degree-bounded base-field polynomials exactly explains a candidate polynomial and
its full agreement set at one affine-line challenge. -/
def HasExactCorrelatedPair (domain : Fin n ↪ F) (f g : Fin n → F) (ι : F →+* E)
    (k : ℕ) (z : E) (P : E[X]) : Prop :=
  ∃ pair : F[X] × F[X],
    pair.1.degree < k ∧ pair.2.degree < k ∧
      P = correlatedPairSpecialization ι z pair ∧
      polynomialAgreementSet (domain.trans ⟨ι, ι.injective⟩)
        (fun i ↦ ι (f i) + z * ι (g i)) P =
          commonPolynomialAgreementSet domain f g pair.1 pair.2

end ReedSolomon
