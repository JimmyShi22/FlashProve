/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TupleSpecialization.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 1 of the 4 declarations of the file is kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
* Lemmas are called by their names in Lean 4.29.1 and this Mathlib: finsetSum_coeff became
  finset_sum_coeff (1 time); mem_ofPred_eq became mem_setOf_eq (1 time).
-/

import ThirdParty.ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement

/-!
# Injective specialization of polynomial tuples

A tuple `P : Fin (ℓ + 1) → F[X]` specializes at a challenge `z` in a field `E`, along
`φ : F →+* E`, to the batched polynomial `∑ t, z ^ t • (P t).map φ`. Two distinct tuples have the
same specialization at only finitely many challenges: comparing the coefficient of `X ^ j` gives
two polynomials of degree at most `ℓ` in `z`, and a polynomial with infinitely many roots is zero.
No bound on `ℓ` or on the characteristic is needed.

Consequently a finite family of tuples specializes injectively at all but finitely many
challenges. Over an infinite field `E` one challenge therefore separates the whole family while
avoiding a finite set of values and the roots of finitely many nonzero polynomials.

## Main statements

* `ReedSolomon.polynomialTuple_eq_of_infinite_specializations`: tuples whose specializations
  agree at infinitely many challenges are equal.
* `ReedSolomon.finite_polynomialTuple_collisions`: distinct tuples collide at finitely many
  challenges.
* `ReedSolomon.finite_polynomialTuple_noninjective_challenges`: a finite family specializes
  injectively at all but finitely many challenges.
* `ReedSolomon.exists_polynomialTuple_specialization_injective_avoiding_roots`: over an infinite
  field, one challenge separates a finite family and avoids finitely many values and roots.
-/

namespace ReedSolomon

open Polynomial

variable {F E : Type*} [Field F] [Field E] {ℓ : ℕ}

/-- If the specializations of two tuples along `φ` agree at infinitely many challenges, the tuples
are equal. -/
theorem polynomialTuple_eq_of_infinite_specializations (φ : F →+* E)
    (P Q : Fin (ℓ + 1) → F[X])
    (h : {z : E | powerBatchedPolynomial (fun t ↦ (P t).map φ) z =
      powerBatchedPolynomial (fun t ↦ (Q t).map φ) z}.Infinite) : P = Q := by
  funext t
  ext j
  have hab : powerBatchedCoordinate (fun t ↦ φ ((P t).coeff j)) =
      powerBatchedCoordinate (fun t ↦ φ ((Q t).coeff j)) := by
    refine eq_of_infinite_eval_eq _ _ (h.mono fun z hz ↦ ?_)
    have hc := congrArg (fun p : E[X] ↦ p.coeff j) hz
    simpa only [Set.mem_setOf_eq, powerBatchedCoordinate_eval, powerBatchedPolynomial,
      finset_sum_coeff, coeff_smul, smul_eq_mul, coeff_map] using hc
  exact φ.injective (congrFun (powerBatchedCoordinate_injective hab) t)

end ReedSolomon
