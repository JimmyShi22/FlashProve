-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/BlocksEight.lean: THE KIND K14's LIST OF SUB-PROTOCOLS IS THERE, AND HAS EIGHT
ENTRIES, wherever what goes out with o_u can be said. Theorems.

WHY. The laws on the shared chain take eight letters b1 … b8 with the premise
hbl : blocks P = some [b1, …, b8]. Here that premise is had, as an existence, from
withU P.S = some sentU (which the same laws ask as hUw), or from the accept of the shared chain's
tests on the list of rounds.
  blocks_eight          withU P.S = some sentU → ∃ b1 … b8, blocks P = some [b1, …, b8].
  blocks_eight_of_ok    the same where every sub-protocol of the seated chain passes its test on
                        the list of rounds (by blocks_said, Johnson/Desc/K14/Law/SplitGiven.lean).
What is not claimed. What the eight are: Johnson/Desc/K14/Blocks.lean says it. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.SplitGiven

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params
open VerifiableInference.Desc (Block)

/-- Whatever `blocks` returns has eight entries. -/
theorem blocks_len (P : P14) (l : List (Block St Unit)) (h : blocks P = some l) :
    ∃ b1 b2 b3 b4 b5 b6 b7 b8, l = [b1, b2, b3, b4, b5, b6, b7, b8] := by
  unfold blocks at h
  dsimp only at h
  cases hw : withU P.S with
  | none =>
    rw [hw] at h
    cases h
  | some w =>
    rw [hw] at h
    cases h
    exact ⟨_, _, _, _, _, _, _, _, rfl⟩

/-- **The eight are there where what goes out with o_u can be said.** -/
theorem blocks_eight (P : P14) (sentU : Array OracleNotice) (h : withU P.S = some sentU) :
    ∃ b1 b2 b3 b4 b5 b6 b7 b8, blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8] := by
  unfold blocks
  dsimp only
  rw [h]
  exact ⟨_, _, _, _, _, _, _, _, rfl⟩

/-- **And where the seated chain's tests on the list of rounds accept.** -/
theorem blocks_eight_of_ok (c : Model.Verify.Chains) (P : P14) (tests : List (Block St Unit))
    (last : List (Block St Unit) → Block St Unit)
    (h : ∀ b ∈ (chainOf c P tests last).blocksInOrder, b.planOk = true) :
    ∃ b1 b2 b3 b4 b5 b6 b7 b8, blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8] := by
  obtain ⟨l, hl⟩ := blocks_said c P tests last h
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ := blocks_len P l hl
  exact ⟨b1, b2, b3, b4, b5, b6, b7, b8, hl⟩

end Desc.K14.Law
