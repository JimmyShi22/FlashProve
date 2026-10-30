/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Pairs/Family.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 1 of the 13 declarations of the file is kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.Data.CodingTheory.ReedSolomon.Agreement

/-!
# Finite families of commonly agreeing pairs and injective specialization

Fix an evaluation domain `domain : ι ↪ F` over a field `F` and two received words
`f g : ι → F`. A pair `(P, Q)` of polynomials of degree below `k` whose common agreement set
with `(f, g)` has at least `k` elements is determined by any `k` of its common agreements: `P` and
`Q` are the Lagrange interpolants of `f` and `g` on those coordinates. So all such pairs lie in
the explicit family `correlatedPairFamily domain f g k` of interpolant pairs over the `k`-element
subsets of `ι`, which has at most `(Fintype.card ι).choose k` members. No finiteness of `F` is
needed.

For a field homomorphism `φ : F →+* E` and a challenge `z : E`, the specialization of a pair is
`P.map φ + C z * Q.map φ`. Two distinct pairs have equal specializations for at most one
challenge. Hence a finite family of distinct pairs is specialized injectively at all but finitely
many challenges, and over an infinite field `E` some challenge does so while avoiding any finite
set and any finite set of roots of nonzero auxiliary polynomials. These specialization statements
are those of `ArkLib.ToMathlib.LinearAlgebra.LineInjectivity` in the `E`-module `E[X]`, with
`C z * R = z • R`.

## Main definitions

* `ReedSolomon.correlatedPairFamily`: the interpolant pairs over all `k`-element samples.
* `ReedSolomon.correlatedPairSpecialization`: `P.map φ + C z * Q.map φ`.

## Main statements

* `ReedSolomon.mem_correlatedPairFamily_iff`: the family is exactly the set of pairs of degree
  below `k` with at least `k` common agreements.
* `ReedSolomon.correlatedPairFamily_card_le`, `ReedSolomon.finite_commonAgreement_pairs`.
* `ReedSolomon.pair_eq_of_correlatedPairSpecialization_eq_at_two`,
  `ReedSolomon.subsingleton_correlatedPair_collisions`,
  `ReedSolomon.finite_correlatedPair_collision_challenges`: two challenges determine a pair.
* `ReedSolomon.exists_correlatedPairSpecialization_injOn_avoiding`,
  `ReedSolomon.exists_correlatedPairSpecialization_injOn_avoiding_roots`: an injective challenge
  over an infinite field.
-/

namespace ReedSolomon

noncomputable section

open Polynomial

section Family

variable {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι] [DecidableEq ι]

end Family

section Specialization

variable {F E : Type*} [Field F] [Field E]

/-- **Specialization of a pair.** The polynomial `P.map φ + C z * Q.map φ` over `E` obtained from
the pair `(P, Q)` over `F` at the challenge `z : E`. -/
def correlatedPairSpecialization (φ : F →+* E) (z : E) (pair : F[X] × F[X]) : E[X] :=
  pair.1.map φ + C z * pair.2.map φ

end Specialization

end

end ReedSolomon
