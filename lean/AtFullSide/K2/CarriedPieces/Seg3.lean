-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/CarriedPieces/Seg3.lean: by Lean's kernel, stretch number 3 of the written list of carried entries is the book's.
-/
import AtFullSide.K2.CarriedLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc (KindName Place)
open ProofFile.Honest
open ProofFile.Honest.K14
open AtFullSide.K14

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- By Lean's kernel. -/
theorem segKept_3 : ((segKept.drop 600).drop 600).drop 600 = ((carriedLit.drop 600).drop 600).drop 600 := by
  unfold segKept rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

end AtFullSide.K2

#print axioms AtFullSide.K2.segKept_3
