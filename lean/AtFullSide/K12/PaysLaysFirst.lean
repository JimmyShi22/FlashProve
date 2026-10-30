-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/PaysLaysFirst.lean: laysB accepts at the public fields of the first chain's proximity test, in the first chain, at the finish that the written places give.

What may say no. laysB reads the book's cut at the place, its rows and entries beyond two parts, what
each part states against what the book has for it, and each entry's stretch against its owner's
count.

Limits.
- The full size alone: closed terms.
- It is at bareJob: the rows, the trees and the state on entry stand idle; laysB reads none of them
  (laysB_congr, K12/StepsAtKey.lean).
- An evaluation in Lean's kernel; no independent checker has replayed it.
- Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.LaysBookFacts
import AtFullSide.K12.FitsAtHeadL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open H2K.Member (piLFull)
open AtFullSide.K14 (rawAheadW rawSegW)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **laysB accepts at the first chain's test**, at the written book, at the finish that the
written places give. An evaluation in Lean's kernel. -/
theorem lays_first_test : (finishW.all fun pl =>
    laysB bookW 0 (bareJob piLFull (membersL pl) (freshL pl) : TestJob Unit Unit)) = true := by
  unfold bookW rawAheadW rawSegW ProofFile.Honest.segmentCarries ProofFile.Honest.linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

end AtFullSide.K12

#print axioms AtFullSide.K12.lays_first_test
