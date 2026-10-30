/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Ordinary/FactorAssembly.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 2 of the 4 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.FactorBudget
import ThirdParty.ArkLib.ToMathlib.MvPolynomial.RadicalSplit

/-!
# Combining ordinary factor exceptional sets

The ordinary mutual correlated agreement argument splits the interpolating polynomial `Q` into
its content radical, which does not involve the root variable `X i`, and its distinct irreducible
factors of positive degree in `X i` (`ArkLib.ToMathlib.MvPolynomial.RadicalSplit`). Each factor
has a set of exceptional challenges bounded by its per-factor charge, and the content radical
vanishes on a set bounded by its height. This file unions these sets and charges the union to the
budget of the whole polynomial for each per-factor charge in
`ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.FactorBudget`.

Each assembly theorem applies `MvPolynomial.exists_exceptional_of_factor_exceptional` followed by
a summation bound: the root degrees of the factors add up to at most the root degree of `Q`
(`MvPolynomial.sum_degreeOf_positiveDegreeFactorClasses_le`), and the heights are assumed to add up
to at most `H`.

## Main statements

* `ReedSolomon.exists_exceptional_ordinaryFactorAssembly`: the combination for the coarse charge
  `ordinaryFactorRaw`.
* `ReedSolomon.exists_exceptional_ordinaryCurveFactorAssembly`: the combination for the
  polynomial-curve charge `ordinaryCurveFactorRaw`.
* `ReedSolomon.exists_exceptional_ordinaryUnifiedPowerFactorAssembly`: the combination for the
  free-retention charge `ordinaryUnifiedPowerFactorRawAt`.

## References

* [DKT26]
-/

open scoped BigOperators
open MvPolynomial

namespace ReedSolomon

variable {R σ W V K Fn : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
  [CommMonoidWithZero K] [NoZeroDivisors K] [FunLike Fn (MvPolynomial σ R) K]
  [MonoidWithZeroHomClass Fn (MvPolynomial σ R) K]

omit [IsDomain R] in
private theorem exists_exceptional_factorAssembly_of_budget
    (i : σ) (Q : MvPolynomial σ R) (hQ : Q ≠ 0)
    (ev : W → V → Fn) (Good : W → V → Prop) (height : MvPolynomial σ R → ℕ)
    (charge : Associates (MvPolynomial σ R) → ℚ) (budget : ℚ)
    (hbudget : (height (radicalContent i Q) : ℚ) +
      ∑ c ∈ positiveDegreeFactorClasses i Q, charge c ≤ budget)
    (hcontent : ∃ ex : Finset W, ex.card ≤ height (radicalContent i Q) ∧
      ∀ w ∉ ex, ∀ v, ev w v (radicalContent i Q) ≠ 0)
    (hfactors : ∀ c ∈ positiveDegreeFactorClasses i Q, ∃ ex : Finset W,
      (ex.card : ℚ) ≤ charge c ∧ ∀ w ∉ ex, ∀ v, ev w v c.rep = 0 → Good w v) :
    ∃ ex : Finset W, (ex.card : ℚ) ≤ budget ∧
      ∀ w ∉ ex, ∀ v, ev w v Q = 0 → Good w v := by
  obtain ⟨contentEx, hcCard, hc⟩ := hcontent
  obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_of_factor_exceptional (α := ℚ) i hQ ev Good
    (height (radicalContent i Q)) charge
    ⟨contentEx, Nat.cast_le.mpr hcCard, hc⟩ hfactors
  exact ⟨ex, hcard.trans hbudget, hgood⟩

/-- Combine the content exception with the exceptions of the distinct positive-root-degree
factors, charging the free-retention charge `ordinaryUnifiedPowerFactorRawAt` with `ell` rows and
retention threshold `L`. The conclusion bounds the exceptional set by the free-retention charge of
the whole polynomial, with root-degree budget `B` and height budget `H`.

The hypothesis `Q ≠ 0` is needed as in `MvPolynomial.exists_exceptional_of_factor_exceptional`.
The hypotheses `0 ≤ theta` and `1 ≤ B` are needed as in
`ordinaryUnifiedPowerFactorRawAt_sum_le`. -/
theorem exists_exceptional_ordinaryUnifiedPowerFactorAssembly
    (i : σ) (Q : MvPolynomial σ R) (hQ : Q ≠ 0)
    (ev : W → V → Fn) (Good : W → V → Prop) (height : MvPolynomial σ R → ℕ)
    (theta : ℚ) (n D ell B H L : ℕ) (htheta : 0 ≤ theta) (hB : 1 ≤ B)
    (hroot : degreeOf i Q ≤ B)
    (hheight : height (radicalContent i Q) +
      ∑ c ∈ positiveDegreeFactorClasses i Q, height c.rep ≤ H)
    (hcontent : ∃ ex : Finset W, ex.card ≤ height (radicalContent i Q) ∧
      ∀ w ∉ ex, ∀ v, ev w v (radicalContent i Q) ≠ 0)
    (hfactors : ∀ c ∈ positiveDegreeFactorClasses i Q, ∃ ex : Finset W,
      (ex.card : ℚ) ≤
        ordinaryUnifiedPowerFactorRawAt theta n D ell (degreeOf i c.rep) (height c.rep) L ∧
      ∀ w ∉ ex, ∀ v, ev w v c.rep = 0 → Good w v) :
    ∃ ex : Finset W, (ex.card : ℚ) ≤ ordinaryUnifiedPowerFactorRawAt theta n D ell B H L ∧
      ∀ w ∉ ex, ∀ v, ev w v Q = 0 → Good w v := by
  have hbudget := ordinaryUnifiedPowerFactorRawAt_sum_le (positiveDegreeFactorClasses i Q)
    (fun c ↦ degreeOf i c.rep) (fun c ↦ height c.rep) theta n D ell B H L
    (height (radicalContent i Q)) htheta hB
    ((sum_degreeOf_positiveDegreeFactorClasses_le i Q).trans hroot) hheight
  exact exists_exceptional_factorAssembly_of_budget i Q hQ ev Good height
    (fun c ↦ ordinaryUnifiedPowerFactorRawAt theta n D ell
      (degreeOf i c.rep) (height c.rep) L)
    (ordinaryUnifiedPowerFactorRawAt theta n D ell B H L) hbudget hcontent hfactors

end ReedSolomon
