-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/CompletenessAndZeroKnowledge/LifeNumberAt135.lean: the error term over the life of one commitment, (commitmentLife copies
sessionsPerCopy).err, at the three numbers 0, 0 and 2^-174, as a number: for at most 710324 copies and at most 688127
sessions on each copy it is below 2^-135. The third number is spelt ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ)), a real power
with a real exponent. Each right side stands in two spellings: ENNReal.ofReal ((2 : ℝ) ^ (-135 : ℝ)), and, in the names
that end in _half, (2⁻¹ : ℝ≥0∞) ^ 135.

  LifeNumberAt135.half_power_of_real   the bridge between the spellings: ENNReal.ofReal (2 ^ (-n)) is (2⁻¹) ^ n
  life_err_at_zero_zero   at 0 and 0 the term is copies · sessionsPerCopy · z
  life_sum                at 710324, 688127 and 2^-174 it is 488793123148 · 2^-174
  life_number_135         the term is at most 2^-135          (488793123148 < 2^39 = 549755813888)
  life_number_135_lt      the term is below 2^-135
  life_number_not_136     control: the term is not at most 2^-136      (488793123148 > 2^38 = 274877906944)
  life_err_mono           at 0 and 0 the term grows with each of the two counts
  life_number_at_most     for copies ≤ 710324 and sessionsPerCopy ≤ 688127 the term is below 2^-135

Limits. Arithmetic alone, from err_commitmentLife (Johnson/T3/WholeViewFollows.lean). That any prover has the numbers 0, 0
and 2^-174 is no part of this file, and neither is anything on what is hidden. 2^-135 is the least power of one half that
the term fits at the two largest counts. The (2⁻¹ : ℝ≥0∞) ^ 135 of E2E/ZetaAtCaps.lean is another quantity, the error after
hashing for placeholder provers; the two only share the exponent.
-/
import Johnson.T3.WholeViewFollows
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Data.ENNReal.Inv
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open scoped ENNReal

namespace VerifiableInference.Compilation

local notation "u" => (2⁻¹ : ℝ≥0∞)

namespace LifeNumberAt135

/-- **The bridge between the two spellings** of a power of one half. -/
theorem half_power_of_real (n : ℕ) : ENNReal.ofReal ((2 : ℝ) ^ (-(n : ℝ))) = u ^ n := by
  have e : (2 : ℝ) ^ (-(n : ℝ)) = ((2 : ℝ)⁻¹) ^ n := by
    rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]
  rw [e, ENNReal.ofReal_pow (by norm_num), ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

theorem half_power_174 : ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ)) = u ^ 174 := by
  have h : (-174 : ℝ) = -((174 : ℕ) : ℝ) := by norm_num
  rw [h, half_power_of_real]

theorem half_power_135 : ENNReal.ofReal ((2 : ℝ) ^ (-135 : ℝ)) = u ^ 135 := by
  have h : (-135 : ℝ) = -((135 : ℕ) : ℝ) := by norm_num
  rw [h, half_power_of_real]

theorem half_power_136 : ENNReal.ofReal ((2 : ℝ) ^ (-136 : ℝ)) = u ^ 136 := by
  have h : (-136 : ℝ) = -((136 : ℕ) : ℝ) := by norm_num
  rw [h, half_power_of_real]

/-- 2^a · 2^-(a+b) = 2^-b. -/
theorem two_pow_mul_half_pow (a b : ℕ) : ((2 ^ a : ℕ) : ℝ≥0∞) * u ^ (a + b) = u ^ b := by
  have c : ((2 ^ a : ℕ) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ a := by norm_num
  rw [c, pow_add, ← mul_assoc, ← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow,
    one_mul]

/-- Multiples of one power of one half compare as the natural numbers in front. -/
theorem nat_mul_half_pow_le_iff (a b n : ℕ) : (a : ℝ≥0∞) * u ^ n ≤ (b : ℝ≥0∞) * u ^ n ↔ a ≤ b := by
  constructor
  · intro h
    have one : (2 : ℝ≥0∞) ^ n * u ^ n = 1 := by
      rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
    have k := mul_le_mul' (le_refl ((2 : ℝ≥0∞) ^ n)) h
    rw [mul_left_comm ((2 : ℝ≥0∞) ^ n) (a : ℝ≥0∞) (u ^ n),
      mul_left_comm ((2 : ℝ≥0∞) ^ n) (b : ℝ≥0∞) (u ^ n), one, mul_one, mul_one] at k
    exact_mod_cast k
  · intro h
    have hc : (a : ℝ≥0∞) ≤ (b : ℝ≥0∞) := by exact_mod_cast h
    exact mul_le_mul' hc le_rfl

theorem nat_mul_half_pow_lt_iff (a b n : ℕ) : (a : ℝ≥0∞) * u ^ n < (b : ℝ≥0∞) * u ^ n ↔ a < b :=
  lt_iff_lt_of_le_iff_le (nat_mul_half_pow_le_iff b a n)

theorem half_135_as_multiple : u ^ 135 = ((2 ^ 39 : ℕ) : ℝ≥0∞) * u ^ 174 :=
  (two_pow_mul_half_pow 39 135).symm

theorem half_136_as_multiple : u ^ 136 = ((2 ^ 38 : ℕ) : ℝ≥0∞) * u ^ 174 :=
  (two_pow_mul_half_pow 38 136).symm

end LifeNumberAt135

open LifeNumberAt135

/-- At 0 for the offline run and 0 for a link, the error of a commitment's life is the number of sessions times the third
number. -/
theorem life_err_at_zero_zero (copies sessionsPerCopy : ℕ) (z : ℝ≥0∞) :
    (commitmentLife copies sessionsPerCopy).err 0 0 z = ((copies * sessionsPerCopy : ℕ) : ℝ≥0∞) * z := by
  rw [err_commitmentLife, mul_zero, add_zero, zero_add]

/-- The term as a multiple of 2^-174. -/
theorem life_sum :
    (commitmentLife 710324 688127).err 0 0 (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) =
      ((488793123148 : ℕ) : ℝ≥0∞) * u ^ 174 := by
  have p : (710324 * 688127 : ℕ) = 488793123148 := by norm_num
  rw [life_err_at_zero_zero, half_power_174, p]

/-- The term is below 2^-135, the right side as a power of 2⁻¹. -/
theorem life_number_135_lt_half :
    (commitmentLife 710324 688127).err 0 0 (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) < u ^ 135 := by
  rw [life_sum, half_135_as_multiple]
  exact (nat_mul_half_pow_lt_iff _ _ _).2 (by norm_num)

/-- The term is at most 2^-135, the right side as a power of 2⁻¹. -/
theorem life_number_135_half :
    (commitmentLife 710324 688127).err 0 0 (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) ≤ u ^ 135 :=
  le_of_lt life_number_135_lt_half

/-- **The term at 710324 copies, 688127 sessions on each, and 0, 0, 2^-174 is below 2^-135.** -/
theorem life_number_135_lt :
    (commitmentLife 710324 688127).err 0 0 (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) <
      ENNReal.ofReal ((2 : ℝ) ^ (-135 : ℝ)) := by
  rw [half_power_135]
  exact life_number_135_lt_half

/-- The same with «at most». -/
theorem life_number_135 :
    (commitmentLife 710324 688127).err 0 0 (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-135 : ℝ)) :=
  le_of_lt life_number_135_lt

/-- Control: the term is above 2^-136, the right side as a power of 2⁻¹. -/
theorem life_number_not_136_half :
    ¬ ((commitmentLife 710324 688127).err 0 0 (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) ≤ u ^ 136) := by
  rw [life_sum, half_136_as_multiple, nat_mul_half_pow_le_iff]
  norm_num

/-- Control: the term is above 2^-136. -/
theorem life_number_not_136 :
    ¬ ((commitmentLife 710324 688127).err 0 0 (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (-136 : ℝ))) := by
  rw [half_power_136]
  exact life_number_not_136_half

/-- At 0 and 0 the term grows with the number of copies and with the number of sessions on each copy. -/
theorem life_err_mono {copies copies' sessionsPerCopy sessionsPerCopy' : ℕ} (hc : copies ≤ copies')
    (hs : sessionsPerCopy ≤ sessionsPerCopy') (z : ℝ≥0∞) :
    (commitmentLife copies sessionsPerCopy).err 0 0 z ≤
      (commitmentLife copies' sessionsPerCopy').err 0 0 z := by
  have hn : copies * sessionsPerCopy ≤ copies' * sessionsPerCopy' := Nat.mul_le_mul hc hs
  have hm : ((copies * sessionsPerCopy : ℕ) : ℝ≥0∞) ≤ ((copies' * sessionsPerCopy' : ℕ) : ℝ≥0∞) :=
    Nat.cast_le.2 hn
  rw [life_err_at_zero_zero copies sessionsPerCopy, life_err_at_zero_zero copies' sessionsPerCopy']
  exact mul_le_mul' hm le_rfl

/-- **For at most 710324 copies and at most 688127 sessions on each, the term at 0, 0, 2^-174 is below 2^-135.** -/
theorem life_number_at_most {copies sessionsPerCopy : ℕ} (hc : copies ≤ 710324)
    (hs : sessionsPerCopy ≤ 688127) :
    (commitmentLife copies sessionsPerCopy).err 0 0 (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) <
      ENNReal.ofReal ((2 : ℝ) ^ (-135 : ℝ)) :=
  lt_of_le_of_lt (life_err_mono hc hs _) life_number_135_lt

/-- The same, the right side as a power of 2⁻¹. -/
theorem life_number_at_most_half {copies sessionsPerCopy : ℕ} (hc : copies ≤ 710324)
    (hs : sessionsPerCopy ≤ 688127) :
    (commitmentLife copies sessionsPerCopy).err 0 0 (ENNReal.ofReal ((2 : ℝ) ^ (-174 : ℝ))) < u ^ 135 :=
  lt_of_le_of_lt (life_err_mono hc hs _) life_number_135_lt_half

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.LifeNumberAt135.half_power_of_real
#print axioms VerifiableInference.Compilation.LifeNumberAt135.half_power_174
#print axioms VerifiableInference.Compilation.LifeNumberAt135.half_power_135
#print axioms VerifiableInference.Compilation.LifeNumberAt135.half_power_136
#print axioms VerifiableInference.Compilation.LifeNumberAt135.two_pow_mul_half_pow
#print axioms VerifiableInference.Compilation.LifeNumberAt135.nat_mul_half_pow_le_iff
#print axioms VerifiableInference.Compilation.LifeNumberAt135.nat_mul_half_pow_lt_iff
#print axioms VerifiableInference.Compilation.LifeNumberAt135.half_135_as_multiple
#print axioms VerifiableInference.Compilation.LifeNumberAt135.half_136_as_multiple
#print axioms VerifiableInference.Compilation.life_err_at_zero_zero
#print axioms VerifiableInference.Compilation.life_sum
#print axioms VerifiableInference.Compilation.life_number_135_lt_half
#print axioms VerifiableInference.Compilation.life_number_135_half
#print axioms VerifiableInference.Compilation.life_number_135_lt
#print axioms VerifiableInference.Compilation.life_number_135
#print axioms VerifiableInference.Compilation.life_number_not_136_half
#print axioms VerifiableInference.Compilation.life_number_not_136
#print axioms VerifiableInference.Compilation.life_err_mono
#print axioms VerifiableInference.Compilation.life_number_at_most
#print axioms VerifiableInference.Compilation.life_number_at_most_half
