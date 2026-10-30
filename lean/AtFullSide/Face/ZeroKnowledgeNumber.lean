-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Face/ZeroKnowledgeNumber.lean: the inequality on numbers that the compiled line on zero
knowledge asks, at the three numbers at which the conditional theorems on the interactive protocol end:
0 for the offline proof, 0 for the link, 2^-174 for the online proof.

  finalZeroKnowledgeError     2^-154: a name for a number. The lines on zero knowledge are stated at it
                       (`zeroKnowledgeOnCanServe`, `zeroKnowledgeAtEveryRequest`,
                       AtFullSide/Face/TheSixLines.lean); the least power of two that fits, no
                       chosen target
  half_pow_ofReal, window_ofReal   the numbers as real numbers
  stops_below_bar      2^-157 + (0 + 0 + 688127 * 2^-174) ≤ 2^-154

Limits. Arithmetic alone. That the online prover's private stops have a share of at most 2^-174 is
another file's. Nothing on zero knowledge.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation

/-- 2^-154. -/
def finalZeroKnowledgeError : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) ^ 154

theorem half_pow_ofReal (n : ℕ) : (2⁻¹ : ℝ≥0∞) ^ n = ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
  rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos (by norm_num),
    ENNReal.ofReal_ofNat]

theorem window_ofReal : ((2 : ℝ) ^ (-174 : ℝ)) = (1 / 2 : ℝ) ^ 174 := by
  rw [Real.rpow_neg (by norm_num), show (174 : ℝ) = ((174 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
    one_div, inv_pow]

/-- **The inequality, at 0, 0 and 2^-174.** -/
theorem stops_below_bar :
    (2⁻¹ : ℝ≥0∞) ^ 157 + (0 + 0 + (688127 : ℕ) * ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) ≤
      finalZeroKnowledgeError := by
  unfold finalZeroKnowledgeError
  rw [half_pow_ofReal, half_pow_ofReal, window_ofReal, zero_add, zero_add,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.finalZeroKnowledgeError
#print axioms VerifiableInference.Compilation.half_pow_ofReal
#print axioms VerifiableInference.Compilation.window_ofReal
#print axioms VerifiableInference.Compilation.stops_below_bar
