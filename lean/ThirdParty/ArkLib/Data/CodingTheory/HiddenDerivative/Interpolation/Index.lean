/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Kai Zhe Zheng
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Index.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 6 of the 33 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.Data.Polynomial.Differential.JetDegree

/-!
# The exact finite interpolation space for hidden-derivative list decoding

For ambient degree `D`, agreement threshold `A`, derivative order `d`, multiplicity `m`, first-jet
cap `M`, and higher-jet budget `W`, the exact interpolation space consists of the differential
polynomials `Q(X, Y₀, ..., Y_d)` whose monomials `X^a Y₀^b₀ ⋯ Y_d^b_d` satisfy

```text
b₁ ≤ M,
sum_{j=2}^d (j - 1) b_j ≤ W,
a + D b₀ + (D - 1) b₁ + ... + (D - d) b_d < m A.
```

The last expression is the `differentialWeight D` weight of the exponent, the same weight that
bounds the degree of a specialization `Q(X, P, P', ...)` for `deg P ≤ D`.

The hypothesis `d < D` is necessary for finiteness: it gives every jet variable weight at least
`D - d > 0`, which bounds the total jet degree by `⌊(mA - 1)/(D - d)⌋`. At `D = d` the variable
`Y_d` has weight zero and all of its powers are eligible. The space is therefore indexed by a
proof of `d < D`, and its canonical monomial basis gives finite coefficient coordinates, the
columns of the local constraint systems.

## Main statements

* `sub_mul_totalJetDegree_le_weight` and `weight_le_add_mul_totalJetDegree`: the specialization
  weight lies between `(D - d) * totalJetDegree u` and `u X + D * totalJetDegree u`.
* `exactInterpolationExponentSet_finite`: the eligible exponents form a finite set when `d < D`.
* `exactInterpolationSpace` with its basis, coordinates, and
  `exactInterpolationCoefficientEvaluator`, which turns a linear map on differential polynomials
  into a map on coefficient columns.
* `differentialWeightedDegree_lt_of_mem_exactInterpolationSpace`,
  `jetTotalDegree_le_floor_of_mem_exactInterpolationSpace`, and
  `jetDegree_le_floor_of_mem_exactInterpolationSpace`: degree bounds for members of the space.
* `finrank_exactInterpolationSpace_eq_card`: its dimension is the number of eligible exponents.

## References

* [Brakensiek, J., Chen, Y., Putterman, A., Zhang, Z., and Zheng, K. Z., *Algorithmic List
  Decoding of Reed–Solomon Codes up to Capacity in the Low-Rate Regime*][BCPZZ26].
* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26], Section 6.1, the support (70).
-/

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {R V : Type*} {d D A m M W : ℕ}

/-! ### Jet weights -/

/-- The weight counting the exponent of `Y₁`. It is zero on every variable when `d = 0`. -/
def jetFirstWeight : JetVariable d → ℕ
  | none => 0
  | some j => if j.val = 1 then 1 else 0

/-- The anisotropic higher-jet weight: `X`, `Y₀`, and `Y₁` have weight zero and `Y_j` has
weight `j - 1`. -/
def jetHigherWeight : JetVariable d → ℕ
  | none => 0
  | some j => j.val - 1

/-- The higher-jet weight `∑_{j ≥ 2} (j - 1) b_j` of a monomial. -/
def fullHigherJetWeight (u : JetVariable d →₀ ℕ) : ℕ :=
  Finsupp.weight jetHigherWeight u

/-- The degree of an exponent splits into the `X` exponent and the total jet degree. -/
theorem degree_eq_add_totalJetDegree (u : JetVariable d →₀ ℕ) :
    u.degree = u none + totalJetDegree u := by
  classical
  simp [Finsupp.degree_eq_sum, totalJetDegree_eq_sum, Fintype.sum_option]

/-- The specialization weight written out: `a + ∑_j (D - j) b_j`. -/
theorem weight_differentialWeight_eq (D : ℕ) (u : JetVariable d →₀ ℕ) :
    Finsupp.weight (differentialWeight D) u =
      u none + ∑ j : Fin (d + 1), (D - j.val) * u (some j) := by
  classical
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, Fintype.sum_option, differentialWeight,
    mul_comm]

/-- The specialization weight is at most the coarse weight `a + D * totalJetDegree u`, since
every jet variable `Y_j` has weight `D - j ≤ D`. This is the upper companion of
`sub_mul_totalJetDegree_le_weight` and needs no hypothesis on `d` or `D`. -/
theorem weight_le_add_mul_totalJetDegree (D : ℕ) (u : JetVariable d →₀ ℕ) :
    Finsupp.weight (differentialWeight D) u ≤ u none + D * totalJetDegree u := by
  rw [weight_differentialWeight_eq, totalJetDegree_eq_sum, Finset.mul_sum]
  exact Nat.add_le_add_left (Finset.sum_le_sum fun j _ => Nat.mul_le_mul_right _ (Nat.sub_le _ _))
    _

/-! ### Eligible exponents -/

/-! ### Space, basis, and coefficient coordinates -/

/-! ### Degree bounds -/

end

end ReedSolomon.HiddenDerivative
