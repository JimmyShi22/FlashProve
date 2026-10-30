-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/ZetaTries.lean: how likely n + 1 tries all fail a proof-of-work test of at most β bits.

Summary. Arithmetic on the written expression `grFailAt` (Johnson/Prover/Law/Defs.lean), which is (1
- 2 ^ -b) ^ (n + 1). No protocol or file is named here.

Main results.
  `grFail_le`: for a test of at most β bits and 2 ^ β · k ≤ n + 1: `grFailAt n (some g) ≤ 2 ^ -k`.

Terms: E2E/HidingTerms.lean.

Limits. A bound on a written expression: that this expression bounds the probability that a search
runs out is proved in Johnson/Prover/Law/Chain.lean. An upper bound, not proved to be tight. No
security property is stated.

Definitions and helper lemmas.
  `real_half`, `half_of_tries`: (1 - 1 / N) ^ N ≤ 1 / 2, in the reals and, for N = 2 ^ β, in ℝ≥0∞.


-/
import Johnson.Prover.Law.Defs
import Mathlib.Analysis.SpecialFunctions.Exponential

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.ZetaAt
open OnBytes.Prover
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- (1 - 1 / N) ^ N ≤ 1 / 2, in the reals. -/
theorem real_half (N : ℕ) (hN : 1 ≤ N) : (1 - 1 / (N : ℝ)) ^ N ≤ 1 / 2 := by
  have h1 : (1 - 1 / (N : ℝ)) ^ N ≤ Real.exp (-1) :=
    Real.one_sub_div_pow_le_exp_neg (by exact_mod_cast hN)
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have h3 : Real.exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) h2
  exact h1.trans h3

/-- The same in ℝ≥0∞, for N a power of two. -/
theorem half_of_tries (β : ℕ) : (1 - ((2 : ℝ≥0∞) ^ β)⁻¹) ^ (2 ^ β) ≤ 2⁻¹ := by
  have e : (1 - ((2 : ℝ≥0∞) ^ β)⁻¹) = ENNReal.ofReal (1 - 1 / ((2 ^ β : ℕ) : ℝ)) := by
    have hp : (0 : ℝ) < ((2 ^ β : ℕ) : ℝ) := by positivity
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one, one_div,
      ENNReal.ofReal_inv_of_pos hp, ENNReal.ofReal_natCast]
    push_cast
    rfl
  rw [e, ← ENNReal.ofReal_pow (by
    have : (1 : ℝ) / ((2 ^ β : ℕ) : ℝ) ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact_mod_cast Nat.one_le_two_pow
    linarith)]
  have h := real_half (2 ^ β) Nat.one_le_two_pow
  calc ENNReal.ofReal ((1 - 1 / ((2 ^ β : ℕ) : ℝ)) ^ 2 ^ β) ≤ ENNReal.ofReal (1 / 2) :=
        ENNReal.ofReal_le_ofReal h
    _ = 2⁻¹ := by
        rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
        norm_num

/-- **The probability that none of n + 1 tries passes a test of at most β bits is at most 2 ^ -k, if
2 ^ β · k ≤ n + 1.** -/
theorem grFail_le {C P : Type} (g : GrW C P) (β k n : ℕ) (hb : g.b ≤ β) (hn : 2 ^ β * k ≤ n + 1) :
    grFailAt n (some g) ≤ (2⁻¹ : ℝ≥0∞) ^ k := by
  show (1 - ((2 : ℝ≥0∞) ^ g.b)⁻¹) ^ (n + 1) ≤ _
  have h1 : (1 - ((2 : ℝ≥0∞) ^ g.b)⁻¹) ≤ 1 - ((2 : ℝ≥0∞) ^ β)⁻¹ :=
    tsub_le_tsub_left (ENNReal.inv_le_inv.2 (pow_le_pow_right₀ (by norm_num) hb)) _
  have h2 : (1 - ((2 : ℝ≥0∞) ^ β)⁻¹) ≤ 1 := tsub_le_self
  calc (1 - ((2 : ℝ≥0∞) ^ g.b)⁻¹) ^ (n + 1) ≤ (1 - ((2 : ℝ≥0∞) ^ β)⁻¹) ^ (n + 1) :=
        pow_le_pow_left₀ (zero_le _) h1 _
    _ ≤ (1 - ((2 : ℝ≥0∞) ^ β)⁻¹) ^ (2 ^ β * k) := pow_le_pow_of_le_one (zero_le _) h2 hn
    _ = ((1 - ((2 : ℝ≥0∞) ^ β)⁻¹) ^ 2 ^ β) ^ k := pow_mul _ _ _
    _ ≤ (2⁻¹ : ℝ≥0∞) ^ k := pow_le_pow_left₀ (zero_le _) (half_of_tries β) _

end AtPublicFiles.ZetaAt

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.ZetaAt.half_of_tries
#print axioms AtPublicFiles.ZetaAt.grFail_le
#print axioms AtPublicFiles.ZetaAt.real_half
