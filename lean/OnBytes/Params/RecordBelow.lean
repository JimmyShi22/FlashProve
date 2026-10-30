-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/RecordBelow.lean: the typed prices of the round of the table's record at the setting
"record with work" are below stated powers of 2.

`recordPrice` (OnBytes/Params/RecordRound.lean) and `smallRecordPrice`
(OnBytes/Params/RecordRoundSmall.lean) are typed numbers, a whole number times a power of 2. By the
planner's exact comparison, evaluated in Lean's kernel (`record_prices_le`), the first is at most 2
^ -178 and the second at most 2 ^ -175, as real numbers (`recordPrice_below`,
`smallRecordPrice_below`).

Main theorems: `record_prices_le`, `recordPrice_below`, `smallRecordPrice_below`.
What is not claimed: what the heads of the two files named above do not claim. That the exponents
are the best whole ones. For proofs only; the program, that is the Lean port built from OnBytes/,
does not import this file.

-/
import OnBytes.Params.RecordRoundSmall

set_option autoImplicit false

namespace OnBytes.Params
open Binary

/-- The planner's exact comparison: the full-size price of the record's round is at most 2 ^ -178,
the small one at most 2 ^ -175. -/
theorem record_prices_le : recordPrice.le (twoTo (-178)) = true ∧
    smallRecordPrice.le (twoTo (-175)) = true := by decide +kernel

/-- **The price of the record's round at the full-size lines is at most 2 ^ -178.** -/
theorem recordPrice_below : ((recordPrice.val : ℚ) : ℝ) ≤ (2 : ℝ) ^ (-178 : ℤ) := by
  have h := le_sound _ _ record_prices_le.1
  rw [val_twoTo] at h
  have h3 := (Rat.cast_le (K := ℝ)).mpr h
  rw [Rat.cast_zpow] at h3
  push_cast at h3
  exact h3

/-- **The price of the record's round at the small lines is at most 2 ^ -175.** -/
theorem smallRecordPrice_below : ((smallRecordPrice.val : ℚ) : ℝ) ≤ (2 : ℝ) ^ (-175 : ℤ) := by
  have h := le_sound _ _ record_prices_le.2
  rw [val_twoTo] at h
  have h3 := (Rat.cast_le (K := ℝ)).mpr h
  rw [Rat.cast_zpow] at h3
  push_cast at h3
  exact h3

end OnBytes.Params

#print axioms OnBytes.Params.record_prices_le
#print axioms OnBytes.Params.recordPrice_below
#print axioms OnBytes.Params.smallRecordPrice_below
