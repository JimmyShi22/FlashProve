-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/PaysSenders.lean: the closing of a segment (K10): the written senders are the ones that the declared rounds name. Kernel evaluations at written values; the terms are in
AtFullSide/K10/PaysWritten.lean.
-/
import AtFullSide.K10.PaysWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open ProofFile.Honest ProofFile.Honest.K10 AtFullSide.K14
open VerifiableInference.Desc.First.Close (Par entries)
open P2Law.ProofPlan (WP)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- At each of the 25 segments the parts that hold a sending are the written ones. -/
theorem senders_written : ((List.range 25).all fun j => sendersE Johnson.AtFull.Desc.Lots.xsW j == sendW j) = true := by
  decide +kernel


end AtFullSide.K10

#print axioms AtFullSide.K10.senders_written
