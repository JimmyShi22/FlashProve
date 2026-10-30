/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedSharpRegularAgreement.lean,
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 4 of the 29 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedComponentRecognition
import ThirdParty.ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TupleSpecialization
import ThirdParty.ArkLib.Data.Polynomial.Differential.BaseChange
import ThirdParty.ArkLib.Data.Polynomial.Differential.RationalTaylorBidegree
import ThirdParty.ArkLib.Data.Polynomial.Differential.TaylorChartGeometry
import ThirdParty.ArkLib.ToMathlib.RingTheory.Nullstellensatz.BidegreeIncidence
/-!
# Sharp regular power-batched agreement bounds

For an order-`r` differential equation over a polynomial ring, put

```text
a = ell + tau*h,
b = 1 + tau*(v-1),
J = h*b^(r+1) + (r+1)*v*a*b^r.
```

The arbitrary-order dimension-sensitive bound is

```text
J * ((n-L+1)/(A-L+1)) * P_r(A)
  + ell*(n-L)*v*b^r*P_r(L),
```

where `P_r(T) = prod_{j<r} (n-k+j+1)/(T-k+j+1)`. The incidence estimate applies away from
admissible tuple graphs. Sharp tuple counting bounds the retained graphs, and each graph
contributes at most `ell * (n-L)` accidental roots. A common regular Taylor center lifts the
fixed-center estimate to every finite family of bad challenges, yielding one finite exceptional
set. At order one, the estimates specialize to Section 5.6, Theorem 5.14 and Corollary 5.15
of [DKTZ26].

## Main statements

* The Taylor numerators, including high cuts, and agreement equations fit one common bidegree
  rectangle. The initial equation uses `initialJetEquation_mem_restrictBidegree` in its tighter
  `(h, v)` rectangle.
* `regularPowerBatchedHighCuts` collects the retained high numerators.
* `finite_powerBatched_regular_points_off_admissible_graphs_card_le_sharp_of_terminal_recognition`
  accepts terminal graph recognition and only requires `k ≤ A`;
  `finite_powerBatched_regular_points_off_admissible_graphs_card_le_sharp_of_exponent` derives
  recognition internally when `k ≤ L`.
* `finite_powerBatchedBadChallenges_card_le_of_tuple_bound_of_exponent` combines supplied
  tuple and off-graph estimates.
* `finite_powerBatchedBadChallenges_card_le_sharp_of_exponent` combines incidence and tuple
  counting; `exists_exceptional_regularPowerBatchedAgreement_sharp_of_exponent` gives one
  exceptional set for all regular bad challenges.
* `regularPowerBatchedAgreementSharpBound_mono_exponent` shows that the explicit agreement budget
  is monotone in the Taylor exponent.
* `regularPowerBatchedCutJetDegree_le_two_mul`,
  `regularPowerBatchedCutChallengeDegree_le_three_mul`, and
  `regularPowerBatchedInitialMixedDegree_le_uniformCaps` bound the cut and mixed degrees under
  explicit caps on the Taylor exponent and stage parameters.

## References

* [DKTZ26]
-/

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial

variable {F E : Type*} [Field F] [Field E] {n ℓ : ℕ}

/-- Challenge-degree bound of the common Taylor rectangle at exponent `τ`. -/
def regularPowerBatchedCutChallengeDegree (ℓ K h : ℕ) (τ : ℕ := 2 * K) : ℕ := ℓ + τ * h

/-- Total-jet-degree bound of the common Taylor rectangle at exponent `τ`. -/
def regularPowerBatchedCutJetDegree (K v : ℕ) (τ : ℕ := 2 * K) : ℕ := 1 + τ * (v - 1)

/-- A joint common Taylor numerator fits the common cut rectangle at exponent `τ`. -/
theorem jointCommonTaylorNumerator_mem_regularPowerBatchedCutBidegree_of_exponent
    {r : ℕ} (center : E) (Q : DifferentialPolynomial E[X] r)
    (ℓ K h v τ : ℕ) (hτ : TaylorExponentSufficient r K τ) (hv : 0 < v)
    (hheight : CoeffNatDegreeLE Q h) (hjet : jetTotalDegree Q ≤ v)
    (l : Fin K) :
    jointCommonTaylorNumerator center Q τ l ∈ restrictBidegree (Fin (r + 1)) E
      (regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ))
      (regularPowerBatchedCutJetDegree K v (τ := τ)) := by
  have hrect := commonTaylorNumeratorOver_mem_restrictBidegree center Q h v K τ
    hτ hheight hv hjet l
  simpa only [jointCommonTaylorNumerator, regularPowerBatchedCutChallengeDegree,
    regularPowerBatchedCutJetDegree] using
      mem_restrictBidegree_mono hrect (Nat.le_add_left _ _) le_rfl

/-- A joint agreement equation with a received polynomial of degree at most `ℓ` fits the
common Taylor cut rectangle at exponent `τ`. -/
theorem jointTaylorAgreementEquation_mem_regularPowerBatchedCutBidegree_of_exponent
    {r : ℕ} (center x : E) (y : E[X]) (Q : DifferentialPolynomial E[X] r)
    (ℓ K h v τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (hy : y.natDegree ≤ ℓ) (hv : 0 < v) (hheight : CoeffNatDegreeLE Q h)
    (hjet : jetTotalDegree Q ≤ v) :
    jointTaylorAgreementEquation center Q K τ (Polynomial.C x) y ∈
      restrictBidegree (Fin (r + 1)) E
        (regularPowerBatchedCutChallengeDegree ℓ K h (τ := τ))
        (regularPowerBatchedCutJetDegree K v (τ := τ)) := by
  simpa only [jointTaylorAgreementEquation, regularPowerBatchedCutChallengeDegree,
    regularPowerBatchedCutJetDegree] using
      taylorAgreementEquationOver_mem_restrictBidegree center x y Q ℓ h v K τ
        hτ hy hheight hv hjet

end ReedSolomon
