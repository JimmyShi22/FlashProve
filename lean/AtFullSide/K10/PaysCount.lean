-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/PaysCount.lean: the closing of a segment (K10): there are 25 closings. Kernel evaluations at written values; the terms are in
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
/-- **There are 25 closings**: so no statement below holds for want of a case. -/
theorem parsW_length : parsW.length = 25 := by decide +kernel


end AtFullSide.K10

#print axioms AtFullSide.K10.parsW_length
