-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/LaysLastTest.lean: laysLastB accepts at the last chain's test at the written book, and so at every job with those public fields at the maker's book.

  lays_W      laysLastB accepts at jobWB
  lays_W_at   so at every job with those fields, at the maker's book

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
open H2K.Member (piWFull)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open AtFullSide.K14 (rawAheadW rawSegW)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **laysLastB accepts at the written book.** An evaluation in Lean's kernel. -/
theorem lays_W : laysLastB bookW jobWB = true := by
  unfold bookW rawAheadW rawSegW ProofFile.Honest.segmentCarries ProofFile.Honest.linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- **At every job with these fields, at the maker's book.** -/
theorem lays_W_at {W X : Type} {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) (J : TestJob W X)
    (hp : J.p = { piWFull with place := placeW })
    (hm : J.members = membersWF) (hf : J.fresh = some (senderW, 1)) : laysLastB B J = true := by
  rw [book_is_written hB]
  rw [laysLastB_congr bookW J jobWB hp hm hf]
  exact lays_W

end AtFullSide.K12

#print axioms AtFullSide.K12.lays_W
#print axioms AtFullSide.K12.lays_W_at
