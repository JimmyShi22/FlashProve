-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/LaysSenderW.lean: the book's tests at W's sender's place: the cut is the part's two moves; no row or entry beyond part 0; no entry hands it anything.

Limits.
- The full size alone: closed terms. An evaluation in Lean's kernel; no independent checker has
  replayed it.
- Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.LaysBookFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open AtFullSide.K14 (rawAheadW rawSegW)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The tests at W's sender's place.** -/
theorem m4_tests :
    bookW.cuts.lookup ⟨1, none, 4, .K1⟩ = some [2] ∧
    (bookW.first.any fun r => r.1.place == ⟨1, none, 4, .K1⟩ && decide (1 ≤ r.1.part)) = false ∧
    (bookW.ahead.any fun e => e.spender.place == ⟨1, none, 4, .K1⟩ && decide (1 ≤ e.spender.part))
      = false ∧
    (bookW.ahead.all fun e => !(e.spender == senderW)) = true := by
  unfold bookW rawAheadW rawSegW ProofFile.Honest.segmentCarries ProofFile.Honest.linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

end AtFullSide.K12

#print axioms AtFullSide.K12.m4_tests
