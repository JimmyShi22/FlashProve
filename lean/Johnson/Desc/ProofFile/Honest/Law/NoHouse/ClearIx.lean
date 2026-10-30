-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/ClearIx.lean: two arithmetic lemmas on the number that the
verifier's step "link l: cleared" has in the first chain's blocksInOrder list (the library's
`P1L20.clearIx`). The file contains no definition.

  1  `clearIx_is`   that number in the form in which `clear_yes_at` and `open_before_cleared`
     (Honest/Law/NoHouse/ClearedYes.lean, ClearedArms.lean) take it
  2  `clearIx_bounds`   it lies between 3 and 355

Limits.
  * The numbers are those of the chain at the full size.
  * No property of a prover or of the protocol is stated or proved.
-/
import Johnson.P1L20R.FrameSits
import Johnson.IMR.WrittenList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread

/-- The number of "link l: cleared", in the form in which `clear_yes_at` takes it. -/
theorem clearIx_is (l : Nat) : P1L20.clearIx l = 14 * l + IM.nAt l + 4 + 2 + 1 := by
  unfold IM.nAt
  show 14 * l + (if l = 24 then 9 else 7) + 7 = _
  omega

/-- That number lies between 3 and 355. -/
theorem clearIx_bounds {l : Nat} (hl : l < 25) : 3 ≤ P1L20.clearIx l ∧ P1L20.clearIx l ≤ 355 := by
  show 3 ≤ 14 * l + (if l = 24 then 9 else 7) + 7 ∧ 14 * l + (if l = 24 then 9 else 7) + 7 ≤ 355
  split <;> omega

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.clearIx_is
#print axioms ProofFile.Honest.FirstThread.clearIx_bounds
