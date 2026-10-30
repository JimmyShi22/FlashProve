/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Local/Coordinates.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 10 of the 26 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
* Lemmas are called by their names in Lean 4.29.1 and this Mathlib: mem_ofPred_eq became
  mem_setOf_eq (1 time).
-/

import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Sym.Card
import ThirdParty.ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.ConstraintMap
import ThirdParty.ArkLib.Data.MvPolynomial.WeightAtMost

/-!
# Reachable coordinates of the local constraint map

The unscaled local substitution sends `X ↦ center + T`, `Y₀ ↦ received + ∑_j ± T^(j+1) Y_(j+1) +
T E`, and `Y_(j+1) ↦ Y_(j+1)`. This file bounds the exponents that can occur in the image, and
uses the bounds to count a finite set of local exponents that contains the support of every local
constraint.

The bounds are all instances of one statement,
`unscaledLocalSubstitution_mem_restrictWeightAtMost`: if a source weight `v` and a local weight
`w` with values in an ordered additive monoid satisfy

```text
0 ≤ v X,   w T ≤ v X,   0 ≤ v Y₀,   w T + w E ≤ v Y₀,
(j + 1) w T + w Y_(j+1) ≤ v Y₀,   w Y_(j+1) ≤ v Y_(j+1),
```

then the substitution maps polynomials of `v`-weight at most `a` to polynomials of `w`-weight at
most `a`. The integer weight `T ↦ -1` lets the negative weight of `T` absorb the higher jets that
the substitution introduces in `Y₀`, which gives, for every monomial `T^t E^h ⋯` in the image:

* `h ≤ t`;
* its higher-jet weight is at most `W + (t - h)` if the source has higher-jet weight at most `W`,
  and the same for the derivative-order weight;
* its jet degree (the degree in `E` and the `Y_j`) is at most the source's total jet degree.

After projecting to contact order `t + d h < m`, the residual `r = t - h` is below `m` and
`h < ⌈(m - r)/(d + 1)⌉`. The finite set `localResidualExponents hd m W B` collects the exponents
allowed by these bounds, and its cardinality is at most `localResidualCoordinateBudget d m W B`.
The cutoff `B` is a natural number; a real cutoff `T` corresponds to `B = ⌈T⌉₊`, since
`n < T ↔ n < ⌈T⌉₊` for natural `n`.

## Main statements

* `unscaledLocalImage_mem_restrictWeightAtMost` and
  `unscaledLocalSubstitution_mem_restrictWeightAtMost`: the weight transport.
* `localE_le_localT_of_mem_support`, `localHigherJetWeight_le_of_mem_support`,
  `localDerivativeJetWeight_le_of_mem_support`, `localJetDegree_le_of_mem_support`, and
  `localJetDegree_lt_of_mem_support`: the bounds on the unscaled image.
* `localConstraintAt_support_of_derivative_weight` and
  `localConstraintAt_support_of_weight_bounds`: the bounds on the support of a local constraint.
* `card_localResidualExponents_le` and `mem_localResidualExponents_of_bounds`.
* `finrank_range_localConstraintAt_domRestrict_le` and
  `finrank_range_exactLocalConstraintAt_le_localResidualCoordinateBudget`: the rank of the local
  constraint map on a space with these bounds is at most the residual budget.
* `localDerivativeExponents`, `card_localDerivativeExponents_le`,
  `mem_localDerivativeExponents_of_bounds`, and
  `finrank_range_localConstraintAt_domRestrict_le_of_derivative_weight`: the same count when the
  source has derivative-order weight at most `W` (weight `j` on `Y_j`, including `Y₁`); then no
  jet-degree cutoff and no hypothesis on `d` is needed.

## References

* [Brakensiek, J., Chen, Y., Putterman, A., Zhang, Z., and Zheng, K. Z., *Algorithmic List
  Decoding of Reed–Solomon Codes up to Capacity in the Low-Rate Regime*][BCPZZ26], Section 3.
-/

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial Finset

variable {R : Type*} [CommRing R] {d : ℕ}

/-! ### Weight transport through the unscaled substitution -/

section Transport

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  {w : LocalVariable d → M} {v : JetVariable d → M}

/-- Each generator image of the unscaled substitution has `w`-weight at most the `v`-weight of
its variable. The nonnegativity hypotheses on `v X` and `v Y₀` are needed for the constants
`center` and `received`; the hypothesis on `(j + 1) w T + w Y_(j+1)` bounds the correction terms
`± T^(j+1) Y_(j+1)` in the image of `Y₀`. -/
theorem unscaledLocalImage_mem_restrictWeightAtMost
    (hX₀ : 0 ≤ v none) (hX : w (localT d) ≤ v none)
    (hY₀ : 0 ≤ v (some 0)) (hE : w (localT d) + w (localE d) ≤ v (some 0))
    (hcorr : ∀ j : Fin d, (j.val + 1) • w (localT d) + w (localY j) ≤ v (some 0))
    (hjet : ∀ j : Fin d, w (localY j) ≤ v (some j.succ))
    (center received : R) (x : JetVariable d) :
    unscaledLocalImage d center received x ∈ restrictWeightAtMost w (v x) := by
  have hXw := fun i => X_mem_restrictWeightAtMost (R := R) w i le_rfl
  rcases x with _ | j
  · exact add_mem (C_mem_restrictWeightAtMost w hX₀ _)
      (X_mem_restrictWeightAtMost w _ hX)
  induction j using Fin.cases with
  | zero =>
    refine add_mem (add_mem (C_mem_restrictWeightAtMost w hY₀ _) ?_)
      (restrictWeightAtMost_mono w hE (mul_mem_restrictWeightAtMost (hXw _) (hXw _)))
    refine Submodule.sum_mem _ fun j _ => restrictWeightAtMost_mono w ?_
      (mul_mem_restrictWeightAtMost (mul_mem_restrictWeightAtMost
        (C_mem_restrictWeightAtMost w le_rfl _) (pow_mem_restrictWeightAtMost (hXw _) _))
        (hXw (localY j)))
    simpa using hcorr j
  | succ j =>
    simpa [unscaledLocalImage] using X_mem_restrictWeightAtMost (R := R) w _ (hjet j)

/-- The unscaled substitution sends polynomials of `v`-weight at most `a` to polynomials of
`w`-weight at most `a`, under the generator hypotheses of
`unscaledLocalImage_mem_restrictWeightAtMost`. -/
theorem unscaledLocalSubstitution_mem_restrictWeightAtMost
    (hX₀ : 0 ≤ v none) (hX : w (localT d) ≤ v none)
    (hY₀ : 0 ≤ v (some 0)) (hE : w (localT d) + w (localE d) ≤ v (some 0))
    (hcorr : ∀ j : Fin d, (j.val + 1) • w (localT d) + w (localY j) ≤ v (some 0))
    (hjet : ∀ j : Fin d, w (localY j) ≤ v (some j.succ))
    (center received : R) {a : M} {Q : DifferentialPolynomial R d}
    (hQ : Q ∈ restrictWeightAtMost v a) :
    unscaledLocalSubstitution d center received Q ∈ restrictWeightAtMost w a :=
  bind₁_mem_restrictWeightAtMost
    (unscaledLocalImage_mem_restrictWeightAtMost hX₀ hX hY₀ hE hcorr hjet center received) hQ

end Transport

/-! ### Bounds on the unscaled image -/

/-- The local weight `T ↦ -1`, `E ↦ 1`, `Y_(j+1) ↦ a j`. -/
private def balancedJetWeight (a : Fin d → ℕ) : LocalVariable d → ℤ
  | none => -1
  | some none => 1
  | some (some j) => a j

/-- The local weight `Y_(j+1) ↦ a j`, zero on `T` and `E`. -/
private def localJetWeight (a : Fin d → ℕ) : LocalVariable d → ℕ
  | some (some j) => a j
  | _ => 0

/-- The source weight `Y_(j+1) ↦ a j`, zero on `X` and `Y₀`. -/
private def sourceJetWeight (a : Fin d → ℕ) : JetVariable d → ℕ
  | none => 0
  | some j => Fin.cases 0 a j

private theorem weight_balancedJetWeight (a : Fin d → ℕ) (e : LocalVariable d →₀ ℕ) :
    e.weight (balancedJetWeight a) =
      (e.weight (localJetWeight a) : ℤ) + e (localE d) - e (localT d) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, balancedJetWeight, localJetWeight, localT,
    localAux]
  ring

/-- If the source has `Y_(j+1)`-weights `a j ≤ j + 1` and weight at most `W`, then every image
monomial `T^t E^h ⋯` has `localJetWeight a` plus `h` at most `W + t`. -/
private theorem localJetWeight_add_le {a : Fin d → ℕ} (ha : ∀ j : Fin d, a j ≤ j.val + 1)
    (center received : R) {W : ℕ} {Q : DifferentialPolynomial R d}
    (hQ : ∀ u ∈ Q.support, u.weight (sourceJetWeight a) ≤ W) {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    e.weight (localJetWeight a) + e (localE d) ≤ W + e (localT d) := by
  have h := unscaledLocalSubstitution_mem_restrictWeightAtMost
    (w := balancedJetWeight a) (v := fun x => (sourceJetWeight a x : ℤ))
    le_rfl (by simp [balancedJetWeight, localT]) le_rfl
    (by simp [balancedJetWeight, sourceJetWeight, localT, localAux])
    (fun j => by
      have := ha j
      simp [balancedJetWeight, sourceJetWeight, localT, localY]
      omega)
    (fun j => by simp [balancedJetWeight, sourceJetWeight, localY]) center received
    (mem_restrictWeightAtMost_natCast_iff.mpr hQ) he
  simp only [Set.mem_setOf_eq, weight_balancedJetWeight] at h
  omega

/-- Every monomial `T^t E^h ⋯` of the unscaled image has `h ≤ t`: the error variable appears only
in the product `T E`. This holds for every polynomial and every center and received value. -/
theorem localE_le_localT_of_mem_support (center received : R) (Q : DifferentialPolynomial R d)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    e (localE d) ≤ e (localT d) := by
  have h := localJetWeight_add_le (a := fun _ => 0) (fun _ => Nat.zero_le _) center received
    (W := 0) (fun u _ => by
      rw [show sourceJetWeight (d := d) (fun _ => 0) = 0 from funext fun x => by
        rcases x with _ | j
        · rfl
        · induction j using Fin.cases <;> rfl]
      simp [Finsupp.weight_apply]) he
  omega

/-- If every source monomial has total jet degree at most `B`, then every image monomial has
degree at most `B` in `E` and the visible jets. -/
theorem localJetDegree_le_of_mem_support (center received : R) {B : ℕ}
    {Q : DifferentialPolynomial R d} (hQ : ∀ u ∈ Q.support, totalJetDegree u ≤ B)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    e.weight (localJetDegreeWeight d) ≤ B :=
  unscaledLocalSubstitution_mem_restrictWeightAtMost (w := localJetDegreeWeight d)
    (v := jetDegreeWeight) le_rfl le_rfl (Nat.zero_le _) le_rfl
    (fun _ => by simp [localJetDegreeWeight, localT, localY, jetDegreeWeight])
    (fun _ => le_rfl) center received hQ he

/-! ### Supports of local constraints -/

/-- A monomial of a local constraint has contact order below `m` and occurs in the unscaled
image. -/
theorem mem_support_of_mem_support_localConstraintAt {m : ℕ} {center received : R}
    {Q : DifferentialPolynomial R d} {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (localConstraintAt m center received Q).support) :
    localContactOrder d e < m ∧ e ∈ (unscaledLocalSubstitution d center received Q).support := by
  rw [mem_support_iff, localConstraintAt, LinearMap.comp_apply, coeff_projectLowContact] at he
  split_ifs at he with h
  · exact ⟨h, mem_support_iff.mpr he⟩
  · exact absurd rfl he

/-! ### Counting the reachable exponents -/

/-! ### Counting the reachable exponents under a derivative-order weight bound -/

end ReedSolomon.HiddenDerivative
