/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedFrobeniusFamily.lean,
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 3 of the 4 declarations of the file are kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerTupleCounting
/-!
# Finite families of admissible Frobenius power tuples

The retained family consists of common-sample interpolants satisfying the Frobenius chart
identities. Its size is bounded by the initial equation's graph-coordinate degree, and one
exceptional challenge set controls exact power agreement for every retained tuple.

## Main statements

* `ReedSolomon.frobeniusRetainedPowerTupleFamily` and
  `ReedSolomon.mem_frobeniusRetainedPowerTupleFamily_iff`: the finite family of admissible
  interpolants and its membership characterization.
* `ReedSolomon.frobeniusRetainedPowerTupleFamily_card_le`: a bound by the initial equation's
  degree in the graph coordinate.
* `ReedSolomon.exists_exceptional_frobeniusRetainedPowerTupleFamily`: one exceptional set gives
  exact power agreement for every retained tuple.

## References

* [DKT26]
-/

noncomputable section

namespace ReedSolomon

open Polynomial PolynomialDifferential

variable {F E α : Type*} [Field F] [Field E] [Fintype α] {k K ℓ : ℕ}

/-- The sample interpolants that satisfy the Frobenius graph identities. -/
def frobeniusRetainedPowerTupleFamily
    (domain : α ↪ F) (values : Fin (ℓ + 1) → α → F)
    (ι : F →+* E) (roots : α → E) (center : E)
    (Q : DifferentialPolynomial E[X] 0) (K k τ s : ℕ) :
    Finset (Fin (ℓ + 1) → F[X]) := by
  classical
  exact (polynomialTupleFamily domain values k).filter
    (IsAdmissibleFrobeniusPowerTuple domain values ι roots center Q K k τ s)

/-- Membership in the retained family is equivalent to Frobenius admissibility. -/
theorem mem_frobeniusRetainedPowerTupleFamily_iff
    (domain : α ↪ F) (values : Fin (ℓ + 1) → α → F)
    (ι : F →+* E) (roots : α → E) (center : E)
    (Q : DifferentialPolynomial E[X] 0) (K k τ s : ℕ)
    (P : Fin (ℓ + 1) → F[X]) :
    P ∈ frobeniusRetainedPowerTupleFamily
      domain values ι roots center Q K k τ s ↔
      IsAdmissibleFrobeniusPowerTuple domain values ι roots center Q K k τ s P := by
  classical
  constructor
  · exact fun h ↦ (Finset.mem_filter.mp h).2
  · intro hP
    obtain ⟨sample, hcard, hagree, _⟩ := hP.sample
    have hcommon : k ≤ (commonCurveAgreementSet domain values P).card := by
      rw [← hcard]
      apply Finset.card_le_card
      intro i hi
      simpa only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ,
        true_and] using hagree i hi
    exact Finset.mem_filter.mpr
      ⟨(mem_polynomialTupleFamily_iff domain values P k).mpr ⟨hP.degree, hcommon⟩, hP⟩

/-- If the initial equation is nonzero and the root, degree, and Taylor-exponent hypotheses hold,
the retained family with `s = p ^ e` has cardinality at most the initial equation's degree in the
graph coordinate. -/
theorem frobeniusRetainedPowerTupleFamily_card_le [Infinite E]
    (domain : α ↪ F) (values : Fin (ℓ + 1) → α → F) (ι : F →+* E)
    (roots : α → E) (center : E) (Q : DifferentialPolynomial E[X] 0)
    (p e τ : ℕ) [ExpChar E p]
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hinit : jointInitialJetEquation center Q ≠ 0) :
    (frobeniusRetainedPowerTupleFamily
      domain values ι roots center Q K k τ (p ^ e)).card ≤
      (jointInitialJetEquation center Q).degreeOf (some 0) := by
  apply admissibleFrobeniusPowerTuples_card_le_degreeOf
    domain values ι roots center Q p e τ hroots hK hKk hτ hinit
  intro P hP
  exact (mem_frobeniusRetainedPowerTupleFamily_iff
    domain values ι roots center Q K k τ (p ^ e) P).mp hP

end ReedSolomon
