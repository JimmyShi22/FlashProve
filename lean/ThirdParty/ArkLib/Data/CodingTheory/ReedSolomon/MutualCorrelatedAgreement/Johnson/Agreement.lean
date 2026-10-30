/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Johnson/Agreement.lean, commit
2817d8c7d2f28d706b17f8de0f885880d0b2eb13. Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* 1 of the 5 declarations of the file is kept. Kept are those that the proofs of
  ReedSolomon.exists_johnson_line_exactCorrelatedPair and
  ReedSolomon.HiddenDerivative.johnsonExceptionCount_le_comparisonEstimate use or name, directly or
  through other declarations, and simp lemmas and instances about those (see ThirdParty/README.md,
  "What was cut"). ArkLib's comment at the top of the file is unchanged and may name declarations
  that are not kept.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import ThirdParty.ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Symbolic.JohnsonCertificate
import ThirdParty.ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.BaseEquation

/-!
# Exact Johnson correlated agreement in every characteristic

A message polynomial has degree at most `D`, so the code dimension is `D + 1`. The Johnson
agreement fraction is `a = √(D / n) + η` with slack `η > 0`. The finite Johnson interpolation
certificate is a nonzero ordinary equation whose roots include every candidate polynomial above the
agreement threshold. The exceptional-challenge bound for ordinary equations then gives one set of
at most `johnsonExceptionCount n D A η` challenges, fixed before the challenge and candidate,
outside which every close candidate `P` on the received line `f + z g` is `P₀ + z P₁` with
`Agr(f + z g, P) = Agr(f, P₀) ∩ Agr(g, P₁)`. The field may be infinite and have any
characteristic.

A weighted Johnson certificate `IsJohnsonWeightedCertificate n D A m B H` with jet cutoff
`B ≤ 2 D + 1` gives the same conclusion with the count
`johnsonWeightedRefinedExceptionCount n D A B H`, through the free-retention charge of ordinary
equations.

## Main statements

* `ReedSolomon.exists_johnson_line_exactCorrelatedPair`: the exceptional-set bound for an
  integer agreement threshold `A ≥ a n`.
* `ReedSolomon.exists_johnson_line_exactCorrelatedPair_ceil`: the same bound at the threshold
  `⌈a n⌉₊`.
* `ReedSolomon.exists_johnson_line_exactCorrelatedPair_of_gap`: when `4 (k - 1) ≤ δ² n` and the
  agreement exceeds `k + δ n`, fewer than `(343 / 3) n²` challenges are exceptional.
* `ReedSolomon.exists_weightedJohnson_line_exactCorrelatedPair`: the exceptional-set bound from a
  weighted Johnson certificate.

## References

* [BCHKS25]
* [DKT26]
-/

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative

open Classical in
/-- **Johnson exact correlated agreement.** For distinct evaluation points and received words
`f g`, one set of at most `johnsonExceptionCount n D A η` challenges is chosen before the challenge
and candidate. Outside it, every polynomial of degree at most `D` agreeing with `f + z g` on at
least `A ≥ (√(D / n) + η) n` points has an exact correlated pair. -/
theorem exists_johnson_line_exactCorrelatedPair
    {F : Type*} [Field F] {n D A : ℕ} {eta : ℝ}
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (hD : 1 ≤ D) (hDn : D ≤ n - 2) (heta : 0 < eta)
    (hthreshold : johnsonAgreement n D eta * n ≤ A) (hAn : A ≤ n) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ johnsonExceptionCount n D A eta ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) (D + 1) z P := by
  classical
  have hDlt : D < n := by omega
  obtain ⟨cert⟩ := exists_johnson_symbolic_certificate hD hDn heta hthreshold
    (k := D + 1) le_rfl domain f g
  have hQ : cert.Q ≠ 0 := by
    intro hz
    apply (cert.specialization_sound (RingHom.id F) 0).1
    rw [hz, map_zero]
  obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_ordinaryEquation_base domain f g cert.Q D
    (johnsonH n D eta) (johnsonMu n D eta) A hQ (by omega)
    (johnsonMu_pos hD hDlt) (johnson_degree_succ_le_agreement hD hDlt heta hthreshold)
    hAn cert.challengeDegree_le cert.jetDegree_le
  have hcardReal : (ex.card : ℝ) ≤
      (ordinaryFactorRaw (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D
        (johnsonMu n D eta) (johnsonH n D eta) : ℝ) := by exact_mod_cast hcard
  refine ⟨ex, ?_, ?_⟩
  · simpa only [ordinaryFactorRaw, johnsonExceptionCount, johnsonTheta, Rat.cast_add,
      Rat.cast_mul, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat] using hcardReal
  · intro z hz P hdegree hagree
    apply hgood z hz P hdegree _ hagree
    have hsound := (cert.specialization_sound (RingHom.id F) z).2
      (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P) P hdegree hagree
      (fun i hi => (Finset.mem_filter.mp hi).2)
    have heval : Polynomial.eval₂RingHom (RingHom.id F) z = (Polynomial.aeval z).toRingHom := by
      apply Polynomial.ringHom_ext
      · intro a
        simp
      · simp
    simpa only [heval, challengeSpecialization] using hsound

end ReedSolomon
