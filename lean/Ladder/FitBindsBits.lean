-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ladder/FitBindsBits.lean: THE GOAL ON BINDING WITH A SECURITY LEVEL, G9bits
(Ladder/Bits.lean), follows from the same record `BindAt` (Ladder/FitBinds.lean) as G9, where the
told committer and `coins` together stay small (2 tMax + qMax + 2 ≤ 2^50): no premise more. Theorems
with proofs.

What this file states.
  `BindsWith.min_one`: a bound on binding may be cut at 1: a probability is at most 1.
  `epsBind_min_le_bitsBinding`: min (`epsBind` tMax (t + qMax)) 1 ≤ `bindingErrorInQueries` t, at every t,
    where 2 tMax + qMax + 2 ≤ 2^50. Arithmetic: 3 (t + 2 tMax + 2)² / 2^256 against 16 (t + 2^23) /
    2^128 + …: where
    16 (t + 2^23) < 2^128 the linear term of `bindingErrorInQueries` pays; elsewhere `bindingErrorInQueries` t ≥ 1. This
    is what the docstring of `bindingErrorInQueries` says in words.
  **`G9bits_of_bindAt`**: the conclusion is the term `G9bits D`.

What it does not show. That a `BindAt` exists at any Z: a conditional. The limits of
Ladder/FitBinds.lean and Johnson/Top/OpensTold.lean hold. The numbers of Ladder/Bits.lean are
choices of this project.

-/
import Ladder.FitBinds
import Ladder.Bits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.Fit
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.K (Pub)
open scoped ENNReal

/-- A bound on binding may be cut at 1. -/
theorem BindsWith.min_one {system : ArgumentSystem}
    {extractor : Commitment → QueryLog → Option system.Weights} {ε : ℕ → ℝ≥0∞}
    (h : BindsWith system extractor ε) : BindsWith system extractor fun t => min (ε t) 1 :=
  fun cq pq St c hc o ho => le_min (h cq pq St c hc o ho) (Prob_le_one _ _)

/-- In numbers: where 16 (t + 2^23) < 2^128 and a ≤ 2^50:
3 (t + a)² ≤ 16 (t + 2^23) · 2^128. -/
theorem three_sq_le (t a : ℕ) (ht : 16 * (t + 2 ^ 23) < 2 ^ 128) (ha : a ≤ 2 ^ 50) :
    3 * (t + a) ^ 2 ≤ 16 * (t + 2 ^ 23) * 2 ^ 128 := by
  have ht' : t < 2 ^ 124 := by
    have : (2 : ℕ) ^ 128 = 16 * 2 ^ 124 := by norm_num
    omega
  have h1 : 3 * t + 6 * a ≤ 2 ^ 132 := by
    have e1 : (2 : ℕ) ^ 132 = 256 * 2 ^ 124 := by norm_num
    have e2 : (2 : ℕ) ^ 50 ≤ 2 ^ 124 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    omega
  have h2 : 3 * a ^ 2 ≤ 2 ^ 155 :=
    le_trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left ha 2)) (by norm_num)
  have e : 3 * (t + a) ^ 2 = t * (3 * t + 6 * a) + 3 * a ^ 2 := by ring
  have e' : 16 * (t + 2 ^ 23) * 2 ^ 128 = t * 2 ^ 132 + 2 ^ 155 := by ring
  rw [e, e']
  exact Nat.add_le_add (Nat.mul_le_mul_left t h1) h2

/-- **`epsBind` at t + qMax, cut at 1, is at most `bindingErrorInQueries` t**, where 2 tMax + qMax + 2 ≤ 2^50:
so where the told committer asks at most `honestBudget` (2^48) queries and `coins` as many. -/
theorem epsBind_min_le_bitsBinding (tMax qMax : ℕ) (hMax : 2 * tMax + qMax + 2 ≤ 2 ^ 50) (t : ℕ) :
    min (epsBind tMax (t + qMax)) 1 ≤ bindingErrorInQueries t := by
  have hpow : ((2 : ℝ≥0∞)⁻¹) ^ 128 = ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
    rw [ENNReal.inv_pow]
  have hlin : ∀ n : ℕ, (n : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 128 = (n : ℝ≥0∞) / 2 ^ 128 := fun n => by
    rw [hpow, ENNReal.div_eq_inv_mul, mul_comm]
  unfold bindingErrorInQueries errorFactorPerQuery verifierQueryAllowance
  rw [hlin]
  by_cases ht : 16 * (t + 2 ^ 23) < 2 ^ 128
  · refine le_trans (min_le_left _ _) (le_trans ?_ le_self_add)
    unfold epsBind
    have key := three_sq_le t (2 * tMax + qMax + 2) ht hMax
    have e1 : t + qMax + 2 * tMax + 2 = t + (2 * tMax + qMax + 2) := by ring
    rw [e1]
    have e2 : ∀ n : ℕ, (n : ℝ≥0∞) / 2 ^ 128 = ((n * 2 ^ 128 : ℕ) : ℝ≥0∞) / 2 ^ 256 := fun n => by
      rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
        show (2 : ℝ≥0∞) ^ 256 = 2 ^ 128 * 2 ^ 128 by rw [← pow_add],
        ENNReal.mul_div_mul_right _ _ (pow_ne_zero 128 (by norm_num))
          (ENNReal.pow_ne_top (by norm_num))]
    rw [e2]
    exact ENNReal.div_le_div_right (Nat.cast_le.2 key) _
  · refine le_trans (min_le_right _ _) (le_trans ?_ le_self_add)
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp)), one_mul]
    exact_mod_cast not_lt.1 ht

/-- **G9bits, FROM `BindAt` AT EVERY Z IN SCOPE**, where 2 tMax + qMax + 2 ≤ 2^50. -/
theorem G9bits_of_bindAt (D : SecondHashFunctionType → Description) (tMax qMax : ℕ)
    (hMax : 2 * tMax + qMax + 2 ≤ 2 ^ 50)
    (B : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      BindAt (atSecondHashFunction D) Z (settingsOfRead pp))
    (commitWithin : ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
      ∀ w ρ, ((atSecondHashFunction D).commit Z (settingsOfRead pp) w ρ).toRandomized.QueryBound honestBudget)
    (hext : ∀ Z pp h₁ h₂, (atSecondHashFunction D).extractor Z (settingsOfRead pp) = (B Z pp h₁ h₂).extractor)
    (count : ∀ Z pp h₁ h₂, (B Z pp h₁ h₂).tS ≤ tMax ∧ (B Z pp h₁ h₂).qCoins ≤ qMax) : G9bits D :=
  fun Z pp h₁ h₂ =>
    ⟨commitWithin Z pp h₁ h₂, BindsWith.mono
      (BindsWith.min_one
        (bindsAt_of_bindAt (atSecondHashFunction D) tMax qMax B commitWithin hext count Z pp h₁ h₂).2)
      fun t => epsBind_min_le_bitsBinding tMax qMax hMax t⟩

end VerifierAndGoals.Fit

#print axioms VerifierAndGoals.Fit.BindsWith.min_one
#print axioms VerifierAndGoals.Fit.three_sq_le
#print axioms VerifierAndGoals.Fit.epsBind_min_le_bitsBinding
#print axioms VerifierAndGoals.Fit.G9bits_of_bindAt
