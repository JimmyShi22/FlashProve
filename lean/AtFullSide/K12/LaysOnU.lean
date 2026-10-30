-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/LaysOnU.lean: laysB accepts at the test on G_u's public fields, in the shared chain, at the typed sizes over the proof file's own codes. It is of the form realSized.all, and realSized is not none (real_members).

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
/-- **laysB at the test on G_u's public fields.** An evaluation in Lean's kernel. -/
theorem lays_U : (VerifiableInference.Desc.K1.realSized.all fun q =>
    laysB bookW 1 (bareJob { H2K.Member.piUFull with place := placeU }
      (membersU (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape)) freshU : TestJob Unit Unit))
    = true := by
  unfold bookW rawAheadW rawSegW ProofFile.Honest.segmentCarries ProofFile.Honest.linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

end AtFullSide.K12

#print axioms AtFullSide.K12.lays_U
