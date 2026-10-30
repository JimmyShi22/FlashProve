-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Bridge/CodeListRSProved.lean: `Cb.BCHKS46` and `Cb.BCHKS46At F E`, proved from two theorems of
ArkLib's, which this file calls by name:
  `ReedSolomon.exists_johnson_line_exactCorrelatedPair`
  (ThirdParty/ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Johnson/Agreement.lean)
  `ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate`
  (ThirdParty/ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/Johnson/FiniteBounds.lean)
The two lie in ThirdParty/ArkLib (126 files adapted from ArkLib,
https://github.com/Verified-zkEVM/ArkLib, commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13,
Apache-2.0; each file there says what was changed). In this library they rest on that folder, on
ThirdParty/MathlibBackport (13 files adapted from Mathlib) and on ThirdParty/ArkLibShim (one file of
our own). AI systems alone adapted and built these files and wrote the files of Cb/Bridge/. That
`Cb.BCHKS46` is the case of two words of Theorem 4.6 of ePrint 2025/2055 is a reading: no theorem
says it (lean/LIMITS.md, L15).
Main names:
  `arkLibEstimate_eq_bchksBound`: ArkLib's comparison estimate equals `Cb.bchksBound` under the
    premises of `BCHKS46`.
  `lineFact : LineFact` (Cb/Bridge/CodeListRSFromLines.lean)
  `bchks46 : Cb.BCHKS46` ; `bchks46At : ∀ F E …, Cb.BCHKS46At F E`

This file and Cb/Bridge/CodeListRSFromLines.lean do not count as written independently of a further
file of ArkLib, which is not in ThirdParty/ArkLib:
ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Johnson/Probability.lean (the same
commit; Copyright ArkLib Contributors, Apache-2.0). The proof of `lineFact` takes the same steps as
passages of two proofs there. There is likeness to two further files of ArkLib as well. The last
two rows of ThirdParty/TAKEN-OVER.tsv tell what this file and Cb/Bridge/CodeListRSFromLines.lean
take over from ArkLib, and from which files.
-/
import Cb.Bridge.CodeListRSFromLines
import ThirdParty.ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
import ThirdParty.ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.Johnson.FiniteBounds

set_option autoImplicit false

namespace Cb.Bridge
open Polynomial ReedSolomon ReedSolomon.HiddenDerivative

/-! ## The bound -/

/-- `est` is ArkLib's comparison estimate. The proof only unfolds definitions. -/
theorem est_eq_arkLib (n D : ℕ) (eta : ℝ) : johnsonComparisonEstimate n D eta = est n D eta := rfl

/-- ArkLib's agreement fraction, written out. The proof only unfolds definitions. -/
theorem agreement_eq_arkLib (n D : ℕ) (eta : ℝ) :
    johnsonAgreement n D eta = Real.sqrt ((D : ℝ) / n) + eta := rfl

/-- **The two bounds are equal.** Under the premises of `BCHKS46`, ArkLib's comparison estimate at
degree bound k and slack 1 - sqrt(k/n) - e/n equals `bchksBound n k e`. Note that this is ArkLib's
comparison estimate. The bound in ArkLib's theorem on lines, `johnsonExceptionCount`, is a different
number, which is at most this one (`arkLibCount_le_est`). -/
theorem arkLibEstimate_eq_bchksBound {n k e : ℕ} (he : 0 < e) (hJ : n * k < (n - e) ^ 2) :
    johnsonComparisonEstimate n k (1 - Real.sqrt ((k : ℝ) / n) - (e : ℝ) / n) = bchksBound n k e :=
  (est_eq_arkLib n k (etaOf n k e)).trans (est_eq_bchks (eta_pos (side he hJ).1 hJ))

/-- The bound in ArkLib's theorem on lines is at most `est`. -/
theorem arkLibCount_le_est {n D A : ℕ} {eta : ℝ} (oneLeD : 1 ≤ D) (dLe : D ≤ n - 2)
    (etaPos : 0 < eta) (fracLe : Real.sqrt ((D : ℝ) / n) + eta ≤ 1)
    (thr : (Real.sqrt ((D : ℝ) / n) + eta) * n ≤ A) :
    johnsonExceptionCount n D A eta ≤ est n D eta :=
  johnsonExceptionCount_le_comparisonEstimate oneLeD dLe etaPos fracLe thr

/-! ## The fact on lines, and the statement -/

/-- **The fact on lines follows from ArkLib's two theorems.** ArkLib speaks of the full set of
positions where a polynomial agrees with a word. A set S on which they agree lies inside that full
set, so ArkLib's threshold is met. ArkLib concludes that the full set equals the set where two
polynomials agree with f and g, so they agree on S too. -/
theorem lineFact : LineFact := by
  intro K _ n D A eta x xInj f g oneLeD dLe etaPos fracLe thr aLe
  classical
  obtain ⟨excl, exclCard, outside⟩ := exists_johnson_line_exactCorrelatedPair
    (F := K) (n := n) (D := D) (A := A) (eta := eta) ⟨x, xInj⟩ f g oneLeD dLe etaPos thr aLe
  refine ⟨excl, exclCard.trans (arkLibCount_le_est oneLeD dLe etaPos fracLe thr), ?_⟩
  intro z zOut p pDeg S sCard onS
  have sSub : S ⊆ polynomialAgreementSet (⟨x, xInj⟩ : Fin n ↪ K) (fun i => f i + z * g i) p := by
    intro j jS
    rw [mem_polynomialAgreementSet]
    exact onS j jS
  obtain ⟨⟨p₀, p₁⟩, deg₀, deg₁, -, sets⟩ := outside z zOut p (by simpa using pDeg)
    (le_trans sCard (Finset.card_le_card sSub))
  refine ⟨p₀, p₁, deg₀, deg₁, fun j jS => ?_⟩
  have jBoth : j ∈ commonPolynomialAgreementSet (⟨x, xInj⟩ : Fin n ↪ K) f g p₀ p₁ := by
    rw [← sets, mem_polynomialAgreementSet]
    exact onS j jS
  exact (mem_commonPolynomialAgreementSet _ _ _ _ _ _).1 jBoth

/-- **`BCHKS46`, proved: agreement of Reed-Solomon codes below the Johnson radius, for every finite
field.** -/
theorem bchks46 : BCHKS46 := bchks46_of_lineFact lineFact

/-- **`BCHKS46At F E`, proved, for all F and E.** -/
theorem bchks46At (F E : Type) [Field F] [Field E] [Finite E] [Algebra F E] : BCHKS46At F E :=
  bchks46At_of_wide bchks46 F E

end Cb.Bridge
