-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/Numbers358.lean: every number below 358 is the number of a
sub-protocol of the first chain at the full size in one of fourteen families. The lemmas of the
several groups of authors speak of a sub-protocol by its number in its family, for example
`14 * l + IM.nAt l + 2` for the batching of segment `l`. The columns of `owesS_head`
(GatherHead.lean) ask something at every `b` below the chain's length. This lemma takes a statement
at each family to the statement at every number. Arithmetic only. No definition.

  1  `nAt_lt`, `nAt_head`   `IM.nAt l` (Johnson/IMR/WrittenList.lean) is 7 for `l` below 24, and 9
     at 24
  2  `all_numbers`   the lemma

The families. 0: the front. In segment `l` below 25, with `n := IM.nAt l`: `14 * l + 1`: "laid";
`14 * l + i + 2` for `i` below `n`: the sub-protocols before the batching; `14 * l + n + 2` to
`14 * l + n + 7`: the batching, the frame's step after it, the one equation, the closing, the shut,
"cleared". 353 to 357: the code switch after the last segment, the proximity test, K13's
sub-protocol, the sending of W, the seal.

Limits.
  * The lemma does not say which sub-protocol stands at a number. The names above are the reading of
    the library's written list of places (`IM.placesW`).
  * Full size only.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.IMR.WrittenList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

theorem nAt_lt {l : Nat} (h : l < 24) : IM.nAt l = 7 := by
  unfold IM.nAt
  rw [if_neg (by omega)]

theorem nAt_head : IM.nAt 24 = 9 := rfl

/-- **A statement at each of the fourteen families holds at every number below 358.** -/
theorem all_numbers (P : Nat → Prop) (hfront : P 0) (hlaid : ∀ l, l < 25 → P (14 * l + 1))
    (hhear : ∀ l, l < 25 → ∀ i, i < IM.nAt l → P (14 * l + i + 2))
    (hback : ∀ l, l < 25 → ∀ j, 2 ≤ j → j ≤ 7 → P (14 * l + IM.nAt l + j))
    (h353 : P 353) (h354 : P 354) (h355 : P 355) (h356 : P 356) (h357 : P 357) :
    ∀ b, b < 358 → P b := by
  intro b hb
  by_cases hA : 353 ≤ b
  · have hc : b = 353 ∨ b = 354 ∨ b = 355 ∨ b = 356 ∨ b = 357 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> assumption
  · by_cases h0 : b = 0
    · rw [h0]
      exact hfront
    · obtain ⟨l, j, hl, hn, hj, rfl⟩ :
          ∃ l j, l < 25 ∧ (IM.nAt l = 7 ∨ IM.nAt l = 9) ∧ j < IM.nAt l + 7 ∧
            b = 14 * l + 1 + j := by
        by_cases hB : 337 ≤ b
        · exact ⟨24, b - 337, by omega, Or.inr nAt_head, by rw [nAt_head]; omega, by omega⟩
        · have hl : (b - 1) / 14 < 24 := by omega
          exact ⟨(b - 1) / 14, (b - 1) % 14, by omega, Or.inl (nAt_lt hl),
            by rw [nAt_lt hl]; omega, by omega⟩
      by_cases j0 : j = 0
      · rw [j0]
        exact hlaid l hl
      · by_cases j1 : j ≤ IM.nAt l
        · have e : 14 * l + 1 + j = 14 * l + (j - 1) + 2 := by omega
          rw [e]
          exact hhear l hl (j - 1) (by omega)
        · have e : 14 * l + 1 + j = 14 * l + IM.nAt l + (j + 1 - IM.nAt l) := by omega
          rw [e]
          exact hback l hl _ (by omega) (by omega)

end ProofFile.Honest

#print axioms ProofFile.Honest.nAt_lt
#print axioms ProofFile.Honest.nAt_head
#print axioms ProofFile.Honest.all_numbers
