-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLBookLineEntries.lean

It states no goal. No property of the protocol is claimed.

A CLOSED LINE over the first chain's
written messages alone (`sentFirstW`, Honest/BookWritten/SentFirst.lean), with the written Booleans in
the plan's stead: the test on the two parts' carried entries says yes at 184 stretches.

  `carriedEntriesTest_written`    **yes at 184**

By what. The labels are read in the manner of `switchCarry_written` (AtFullSide/K14/SwitchesLend.lean):
`linkOf` unfolded, `splitOn_eq`, `slice_toNat?_eq` (Johnson/Unfolds/), then Lean's kernel.

Limits.
- The plan is not read here: that the Booleans are the plan's is `foldFlags_written`.
- The sendings are found by labels (the limits of BookCarryKit.lean and SentFirst.lean stand).
- The full size alone. Nothing on the value of a coin. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLBookLineWritten
import Johnson.Desc.ProofFile.Honest.BookWritten.SentFirst
import AtFullSide.K14.SwitchesLend

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **Yes at 184.** -/
theorem carriedEntriesTest_written :
    carriedEntriesTest (carriesByFlags (foldFlagsW.map (·.1)) sentFirstW ⟨⟨1, none, 1, .K2⟩, 0⟩)
      (carriesByFlags (foldFlagsW.map (·.2)) sentFirstW ⟨⟨1, none, 2, .K12⟩, 1⟩)
      ⟨⟨1, none, 1, .K2⟩, 0⟩ 184 = true := by
  unfold carriedEntriesTest carriesByFlags linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.carriedEntriesTest_written
