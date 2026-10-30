-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLBookClosingEntries.lean

It states no goal. No property of the protocol is claimed.

A CLOSED LINE over the first chain's
written messages (`sentFirstW`) and the written finish (`finishW`), with the written Booleans in the
plan's stead: the body of `closingBookTest` says yes.

  `closingCarriedTest_written`

By what. As `carriedEntriesTest_written` (LotLBookLineEntries.lean): `linkOf` unfolded, `splitOn_eq`,
`slice_toNat?_eq` (Johnson/Unfolds/), then Lean's kernel.

Limits.
- The plan is not read here: that the Booleans are the plan's is `foldFlags_written`.
- The sendings are found by labels (the limits of BookCarryKit.lean and SentFirst.lean stand).
- The full size alone. Nothing on the value of a coin. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLBookClosingLetters
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLBookLineWritten
import Johnson.Desc.ProofFile.Honest.BookWritten.SentFirst
import AtFullSide.K14.SwitchesLend
import AtFullSide.K12.FitsAtHeadL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The closed line**: yes at the written finish. -/
theorem closingCarriedTest_written : finishW.any (fun p => closingCarriedTest
    (carriesByFlags (foldFlagsW.map (·.2)) sentFirstW ⟨⟨1, none, 2, .K12⟩, 1⟩)
    (carriesByFlags (foldFlagsW.map (·.1)) sentFirstW ⟨⟨1, none, 1, .K2⟩, 0⟩) p) = true := by
  unfold closingCarriedTest carriesByFlags linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.closingCarriedTest_written
