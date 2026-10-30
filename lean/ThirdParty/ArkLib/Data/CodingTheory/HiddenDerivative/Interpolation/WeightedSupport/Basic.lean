/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/WeightedSupport/Basic.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 11 of the 17 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Sym.Card
import ThirdParty.ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Index

/-!
# The weighted interpolation support

For a positive weight `D`, a higher-jet budget `W : ℕ` and a real cutoff `L`, an exponent
`X^a Y₀^b₀ ⋯ Y_d^b_d` is *weighted-support eligible* when

```text
sum_{j=2}^d (j - 1) b_j ≤ W,
a + D (b₀ + ⋯ + b_d) < L.
```

The first inequality is the higher-jet budget of the exact interpolation space of
`Interpolation/Index.lean`. The second is a strict cutoff on the coarse weight
`a + D * totalJetDegree u`. Unlike the exact space there is no cap on the exponent of `Y₁` and no
lower bound on any jet degree; the cutoff alone makes the support finite once `0 < D`, since then
the ordinary degree `a + totalJetDegree u` is at most the coarse weight. The weighted support
space is the space of differential polynomials whose monomials are all eligible.

In the capacity construction the cutoff is `L = m * D * (1 + g)`. Dividing by `D` bounds the total
jet degree by `L / D`, and the coarse weight dominates the specialization weight
`Finsupp.weight (differentialWeight D)`, so members of the space satisfy the decoder's degree
budgets directly.

## Main statements

* `WeightedSupportEligible`, `weightedSupportExponents`, `weightedSupportSpace` and
  `weightedSupportSpaceBasis`, with `weightedSupportEligible_finite`, the `Module.Finite`
  instance and `finrank_weightedSupportSpace_eq_card`.
* `totalJetDegree_lt_of_weightedSupportEligible` and
  `totalJetDegree_le_pred_of_weightedSupportEligible`: the cutoff bounds the total jet degree by
  `L / D`.
* `weightedSupportSpace_le_exactInterpolationSpace`: the weighted support space lies in the exact
  interpolation space when `L ≤ m * A` and `L ≤ D * M`.
* `differentialWeightedDegree_lt_of_mem_weightedSupportSpace`,
  `jetTotalDegree_lt_of_mem_weightedSupportSpace` and
  `decoder_bounds_of_mem_weightedSupportSpace`: degree budgets of members of the space.

The coordinate description and the dimension lower bound are in `WeightedSupport/Dimension.lean`.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26], Section 6.1, the support (70).
-/

open PolynomialDifferential

namespace ReedSolomon.HiddenDerivative

noncomputable section

variable {F : Type*} {d D W : ℕ} {L : ℝ}

/-! ### Eligible exponents -/

/-- An exponent `u` is weighted-support eligible when its higher-jet weight
`∑_{j ≥ 2} (j - 1) u(Y_j)` is at most `W` and its coarse weight `u X + D * totalJetDegree u` is
strictly below the real cutoff `L`. -/
def WeightedSupportEligible (D d W : ℕ) (L : ℝ) (u : JetVariable d →₀ ℕ) : Prop :=
  fullHigherJetWeight u ≤ W ∧ ((u none + D * totalJetDegree u : ℕ) : ℝ) < L

/-- If `0 < D`, an eligible exponent has ordinary degree below `⌈L⌉₊`: the degree
`u X + totalJetDegree u` is at most the coarse weight. The hypothesis is needed, since for
`D = 0` every power of `Y₀` is eligible when `0 < L`. -/
theorem degree_lt_ceil_of_weightedSupportEligible (hD : 0 < D) {u : JetVariable d →₀ ℕ}
    (hu : WeightedSupportEligible D d W L u) : u.degree < ⌈L⌉₊ := by
  rw [degree_eq_add_totalJetDegree]
  have hmul : totalJetDegree u ≤ D * totalJetDegree u := Nat.le_mul_of_pos_left _ hD
  exact (Nat.add_le_add_left hmul _).trans_lt (Nat.lt_ceil.mpr hu.2)

/-- If `0 < D`, there are finitely many eligible exponents. See
`degree_lt_ceil_of_weightedSupportEligible` for why `0 < D` is needed. -/
theorem weightedSupportEligible_finite (hD : 0 < D) :
    {u : JetVariable d →₀ ℕ | WeightedSupportEligible D d W L u}.Finite :=
  (Finsupp.finite_of_degree_le ⌈L⌉₊).subset fun _ hu =>
    (degree_lt_ceil_of_weightedSupportEligible hD hu).le

/-- The finite set of weighted-support eligible exponents. It is specified through
`Set.Finite.toFinset`, so it is not an executable enumeration. -/
def weightedSupportExponents (D d W : ℕ) (L : ℝ) (hD : 0 < D) : Finset (JetVariable d →₀ ℕ) :=
  (weightedSupportEligible_finite (d := d) (W := W) (L := L) hD).toFinset

/-- Membership in `weightedSupportExponents` is `WeightedSupportEligible`. -/
@[simp]
theorem mem_weightedSupportExponents {hD : 0 < D} {u : JetVariable d →₀ ℕ} :
    u ∈ weightedSupportExponents D d W L hD ↔ WeightedSupportEligible D d W L u := by
  simp [weightedSupportExponents]

/-! ### The space and its dimension -/

/-- The differential polynomials whose monomials are all weighted-support eligible. -/
def weightedSupportSpace (F : Type*) [CommSemiring F] (D d W : ℕ) (L : ℝ) (hD : 0 < D) :
    Submodule F (DifferentialPolynomial F d) :=
  MvPolynomial.restrictSupport F
    (↑(weightedSupportExponents D d W L hD) : Set (JetVariable d →₀ ℕ))

/-- Membership in the weighted support space is eligibility of every support exponent. -/
theorem mem_weightedSupportSpace_iff [CommSemiring F] {hD : 0 < D}
    {Q : DifferentialPolynomial F d} :
    Q ∈ weightedSupportSpace F D d W L hD ↔ ∀ u ∈ Q.support, WeightedSupportEligible D d W L u := by
  rw [weightedSupportSpace, MvPolynomial.mem_restrictSupport_iff]
  simp only [Set.subset_def, Finset.mem_coe, mem_weightedSupportExponents]

/-- The monomial basis of the weighted support space, indexed by the eligible exponents. -/
def weightedSupportSpaceBasis (F : Type*) [CommSemiring F] (D d W : ℕ) (L : ℝ) (hD : 0 < D) :
    Module.Basis ↥(weightedSupportExponents D d W L hD) F (weightedSupportSpace F D d W L hD) :=
  MvPolynomial.basisRestrictSupport (R := F)
    (↑(weightedSupportExponents D d W L hD) : Set (JetVariable d →₀ ℕ))

/-- The weighted support space is a finite module: `weightedSupportSpaceBasis` is indexed by the
finite set `weightedSupportExponents D d W L hD`. -/
instance [CommSemiring F] (hD : 0 < D) : Module.Finite F (weightedSupportSpace F D d W L hD) :=
  Module.Finite.of_basis (weightedSupportSpaceBasis F D d W L hD)

/-! ### Degree bounds -/

/-- If `L ≤ B`, an eligible exponent has specialization weight below `B`, since the
specialization weight is at most the coarse weight (`weight_le_add_mul_totalJetDegree`). -/
theorem weight_differentialWeight_lt_of_weightedSupportEligible {B : ℕ} (hL : L ≤ B)
    {u : JetVariable d →₀ ℕ} (hu : WeightedSupportEligible D d W L u) :
    Finsupp.weight (differentialWeight D) u < B :=
  (weight_le_add_mul_totalJetDegree D u).trans_lt (by exact_mod_cast hu.2.trans_le hL)

/-- If `L ≤ B`, every member of the weighted support space has specialization-weighted degree
below `B`. The hypothesis `0 < B` covers the zero polynomial, whose weighted degree is `0`. -/
theorem differentialWeightedDegree_lt_of_mem_weightedSupportSpace [CommSemiring F] {B : ℕ}
    {hD : 0 < D} (hB : 0 < B) (hL : L ≤ B) {Q : DifferentialPolynomial F d}
    (hQ : Q ∈ weightedSupportSpace F D d W L hD) : differentialWeightedDegree D Q < B := by
  rw [differentialWeightedDegree, MvPolynomial.weightedTotalDegree, Finset.sup_lt_iff hB]
  exact fun u hu => weight_differentialWeight_lt_of_weightedSupportEligible hL
    (mem_weightedSupportSpace_iff.mp hQ u hu)

end

end ReedSolomon.HiddenDerivative
