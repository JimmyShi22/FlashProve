-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RecCompile/Level.lean: THE BOUND epsC IN THE LIBRARY's FORM OF LEVELS, at λ = 256 and round
errors 2^-128 with the samplers' bias (1 + 2^-64)^K:
if K · 8 ≤ 2^64, j ≤ 126 and tC + tP + tVC W + 2 ≤ 2^j, then epsC W ((1 + 2^-64)^K · 2^-128) tC tP ≤
2^-(127 - j). By the library's arithmetic level_arith, inv_pow_split (Johnson/Thin/K/Level/Arith.lean) and
kapSl_pow_le (Iop/DrawKap.lean). So the bound is below 1 as soon as the two numbers K and tVC W are
known to be small: THESE TWO NUMERALS ARE NOT GIVEN HERE for any object.

-/
import Johnson.RecCompile.CmsGlue
import Johnson.Thin.K.Level.Arith
import Iop.DrawKap

set_option autoImplicit false

noncomputable section

namespace Compile.Batch.Cms
open Iop Rom Prob TopC
open scoped ENNReal

variable {I X : Type} {L : HolographicProtocol I X}

theorem level_pow' (T j : ℕ) (hj : j ≤ 127) (hT : T ≤ 2 ^ j) :
    (T : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 127)⁻¹ ≤ ((2 : ℝ≥0∞) ^ (127 - j))⁻¹ := by
  have e := inv_pow_split (127 - j) j
  rw [Nat.sub_add_cancel hj] at e
  rw [e]
  exact mul_le_mul' (by exact_mod_cast hT) le_rfl

theorem epsC_level (W : QueryLayout 256 L.carrierC) (K j tC tP : ℕ) (hK : K * 2 ^ 3 ≤ 2 ^ 64)
    (hj : j ≤ 126) (hT : tC + tP + tVC W + 2 ≤ 2 ^ j) :
    epsC W (kapSl 64 ^ K * ((2 : ℝ≥0∞) ^ 128)⁻¹) tC tP ≤ ((2 : ℝ≥0∞) ^ (127 - j))⁻¹ := by
  have hc : kapSl 64 ^ K ≤ 1 + (4 : ℝ≥0∞)⁻¹ :=
    (kapSl_pow_le (sl := 64) (n := K) (e := 2) hK).trans (le_of_eq (by norm_num))
  have hT126 : tC + tP + tVC W + 2 ≤ 2 ^ 126 :=
    hT.trans (Nat.pow_le_pow_right (by norm_num) hj)
  calc
    epsC W (kapSl 64 ^ K * ((2 : ℝ≥0∞) ^ 128)⁻¹) tC tP
        = ((tC + tP + tVC W + 1 : ℕ) : ℝ≥0∞) * (kapSl 64 ^ K * ((2 : ℝ≥0∞) ^ 128)⁻¹) +
          2 * ((tC + tP + tVC W + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 := rfl
    _ ≤ ((tC + tP + tVC W + 2 : ℕ) : ℝ≥0∞) * (kapSl 64 ^ K * ((2 : ℝ≥0∞) ^ 128)⁻¹) +
          2 * ((tC + tP + tVC W + 2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
        add_le_add (mul_le_mul' (Nat.cast_le.2 (Nat.le_succ _)) le_rfl) le_rfl
    _ ≤ ((tC + tP + tVC W + 2 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 127)⁻¹ :=
        level_arith _ hT126 _ hc
    _ ≤ ((2 : ℝ≥0∞) ^ (127 - j))⁻¹ := level_pow' _ j (by omega) hT

end Compile.Batch.Cms

#print axioms Compile.Batch.Cms.epsC_level
