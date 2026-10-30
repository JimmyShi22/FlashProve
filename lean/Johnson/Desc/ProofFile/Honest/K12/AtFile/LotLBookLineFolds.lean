-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLBookLineFolds.lean

It states no goal. No property of the protocol is claimed.

ONE CLOSED LINE over the written first
chain's plan: at the 26 rounds in which a link's fresh table is sent (`rawFreshRounds`,
AtFullSide/K14/RawFactsWritten.lean): the last code switch's part is the part that sends what the fold
leaves behind the 25th of them and nothing else; the closing proximity test's second part is that
behind the 26th and nothing else.

  `foldFlags_written`  **the closed line**, against `foldFlagsW` (LotLBookLineWritten.lean)

By what. Lean's kernel, in the manner of `rawBehind_all` (the same file of the library). One kernel
line in this file, on purpose: two side by side double the room.

Limits.
- A fact on written values: WP's own limit stands (Johnson/AtFull/ProofPlan/WP.lean).
- The full size alone. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLBookLineWritten
import AtFullSide.K14.RawFactsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open P2Law.ProofPlan (WP)
open AtFullSide.K14 (rawFreshRounds)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **THE CLOSED LINE.** -/
theorem foldFlags_written :
    (rawFreshRounds.map (foldFlagsAtTwo (planOf WP.first.blocksInOrder) ⟨⟨1, none, 1, .K2⟩, 0⟩
      ⟨⟨1, none, 2, .K12⟩, 1⟩) == foldFlagsW) = true := by
  decide +kernel

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.foldFlags_written
