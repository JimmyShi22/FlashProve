-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/M1/LotsW.lean: the door's form at W's sender, by Lean's kernel, at the written entries rawAheadW.
-/
import AtFullSide.M1.LotsForm
import Johnson.HB.LLHARD.PlanAtQFull

set_option autoImplicit false

namespace AtFullSide.M1
open ProofFile.Honest ProofFile.Honest.K1 ProofFile.Honest.K14 AtFullSide.K14
open OnBytes.SendSim.At OnBytes.SendSim.Seat
open P2Law.ProofPlan (WP)
open VerifiableInference.Desc.K1 (qFull)

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem ok_w :
    okFast (VerifiableInference.Desc.K1.parW qFull VerifiableInference.Desc.K13.Law.gpFull 4 VerifiableInference.Desc.K13.Law.wMsgFull)
      (rideOf (wFold qFull.lin)) aheadBook (orderOf WP) oW = true := by
  unfold aheadBook rawAheadW rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

end AtFullSide.M1

#print axioms AtFullSide.M1.ok_w
