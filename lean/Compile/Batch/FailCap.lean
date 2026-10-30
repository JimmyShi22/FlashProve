-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/FailCap.lean: with the cap `cap64` of 2^(b + 7) attempts (Iop/GrindCap.lean, with its
limits; 64: the numbers below 2^64 as nonces) the term for a failed search is at most 2^-128,
whatever the number b of proof-of-work bits.

  `failBits_cap64_le`  failBits cap64 b ≤ (2^128)⁻¹ for every b (`failBits`,
                       Compile/Batch/FitGrind.lean: (1 − 2^-b)^(mo b + 1), 0 at b = 0; `cap64`:
                       Iop/GrindCap.lean).

Proof: (1 − 2^-b)^(2^b · 2^7) ≤ (1/2)^128 (Prob/PowHalf.lean). The exponent, up to 2^39 at 32 bits,
is never evaluated.

Limits: the term is about e^-128, near 2^-184; the bound here is the short proof's. That the term is
the probability that a search fails is part of the compiler theorem's completeness clause (α:
`alphaBG`, Compile/Batch/SpecGrind.lean), not of this file.
-/
import Compile.Batch.FitGrind
import Iop.GrindCap
import Prob.PowHalf

open scoped ENNReal

namespace Compile.Batch
open Iop

theorem failBits_cap64_le : ∀ b : ℕ, failBits cap64 b ≤ ((2 : ℝ≥0∞) ^ 128)⁻¹
  | 0 => zero_le _
  | b + 1 => by
      show (1 - ((2 : ℝ≥0∞) ^ (b + 1))⁻¹) ^ (cap64.mo (b + 1) + 1) ≤ _
      have e : cap64.mo (b + 1) + 1 = 2 ^ (b + 1) * 128 := by
        rw [cap64_tries, pow_add (2 : ℕ) (b + 1) 7]; norm_num
      rw [e]
      have h := Prob.one_sub_inv_pow_mul_le (n := 2 ^ (b + 1)) (by positivity) 128
      rwa [Nat.cast_pow, Nat.cast_ofNat] at h

end Compile.Batch
