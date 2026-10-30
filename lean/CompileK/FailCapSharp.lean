-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/FailCapSharp.lean: with the programs' cap of 2^(b + 7) tries the term for a failed search
is at most 2^-184, whatever the number b of test bits.

Statements and proofs. Nothing assumed beyond the hypotheses of the statements and whatever the
arguments hold as proofs.
The search is the honest prover's, for a nonce, in a round with test bits (Iop/GrindWire.lean).

Main names:
  `Spec.failBits_cap64_sharp`: failBits cap64 b ≤ (2^184)⁻¹ for every b; `failBits_cap64_le`
    (Compile/Batch/FailCap.lean) has 2^-128. `failBits` (Compile/Batch/FitGrind.lean) is
    (1 - 2^-b)^(mo b + 1), 0 at b = 0; for `cap64` (Iop/GrindCap.lean)
    mo b + 1 = 2^(b + 7) = 2^b · 128.
  `Spec.one_sub_inv_pow_exp`: 0 < n ⇒ (1 - 1/n)^(n k) ≤ exp (-k).
  `Spec.exp_neg_128`: exp (-128) ≤ 2^-184, since 184 · log 2 < 184 · 0.6931471808 = 127.54 ≤ 128.

184 is the best whole exponent for all b: the terms increase with b to exp (-128) = 2^-184.665 (by
arithmetic, not by a theorem: at 9 bits already 2^-184.85).

Limits: this file does not say that the term is the chance that a search fails; that is part of the
compiler theorem's completeness clause (`Spec.completeBatchUGr`, Compile/Batch/SpecUGr.lean;
`cFail_grind`, Compile/Batch/FitGrind.lean).

Terms: lean/GLOSSARY.md.
-/
import Compile.Batch.FailCap

set_option autoImplicit false

open scoped ENNReal

namespace Prob

namespace Spec

def one_sub_inv_pow_exp : Prop :=
  ∀ (n : ℕ),
    0 < n → ∀ k : ℕ, (1 - ((n : ℕ) : ℝ≥0∞)⁻¹) ^ (n * k) ≤ ENNReal.ofReal (Real.exp (-(k : ℝ)))

def exp_neg_128 : Prop := ENNReal.ofReal (Real.exp (-((128 : ℕ) : ℝ))) ≤ ((2 : ℝ≥0∞) ^ 184)⁻¹

end Spec

theorem one_sub_inv_pow_exp : Spec.one_sub_inv_pow_exp := by
  intro n hn k
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : (1 : ℝ≥0∞) - ((n : ℕ) : ℝ≥0∞)⁻¹ = ENNReal.ofReal (1 - (n : ℝ)⁻¹) := by
    rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one,
      ENNReal.ofReal_inv_of_pos hn', ENNReal.ofReal_natCast]
  have h0 : 0 ≤ 1 - (n : ℝ)⁻¹ := sub_nonneg.2 (inv_le_one_of_one_le₀ (by exact_mod_cast hn))
  rw [hx, ← ENNReal.ofReal_pow h0]
  refine ENNReal.ofReal_le_ofReal ?_
  calc
    (1 - (n : ℝ)⁻¹) ^ (n * k) ≤ (Real.exp (-(n : ℝ)⁻¹)) ^ (n * k) :=
      pow_le_pow_left₀ h0 (Real.one_sub_le_exp_neg _) _
    _ = Real.exp (-(k : ℝ)) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      field_simp

theorem exp_neg_128 : Spec.exp_neg_128 := by
  have h1 : (2 : ℝ) ^ 184 ≤ Real.exp 128 := by
    have e : (2 : ℝ) ^ 184 = Real.exp (184 * Real.log 2) := by
      rw [mul_comm, Real.exp_mul, Real.exp_log (by norm_num)]
      norm_cast
    rw [e]
    exact Real.exp_le_exp.2 (by have := Real.log_two_lt_d9; linarith)
  have h2 : Real.exp (-((128 : ℕ) : ℝ)) ≤ ((2 : ℝ) ^ 184)⁻¹ := by
    rw [Real.exp_neg]
    push_cast
    exact inv_anti₀ (by positivity) h1
  have e2 : ((2 : ℝ≥0∞) ^ 184)⁻¹ = ENNReal.ofReal (((2 : ℝ) ^ 184)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_ofNat]
  unfold Spec.exp_neg_128
  rw [e2]
  exact ENNReal.ofReal_le_ofReal h2

end Prob

namespace Compile.Batch
open Iop

def Spec.failBits_cap64_sharp : Prop := ∀ b : ℕ, failBits cap64 b ≤ ((2 : ℝ≥0∞) ^ 184)⁻¹

theorem failBits_cap64_sharp : Spec.failBits_cap64_sharp
  | 0 => zero_le _
  | b + 1 => by
      show (1 - ((2 : ℝ≥0∞) ^ (b + 1))⁻¹) ^ (cap64.mo (b + 1) + 1) ≤ _
      have e : cap64.mo (b + 1) + 1 = 2 ^ (b + 1) * 128 := by
        rw [cap64_tries, pow_add (2 : ℕ) (b + 1) 7]; norm_num
      rw [e]
      have h := Prob.one_sub_inv_pow_exp (2 ^ (b + 1)) (by positivity) 128
      rw [Nat.cast_pow, Nat.cast_ofNat] at h
      exact h.trans Prob.exp_neg_128

end Compile.Batch
