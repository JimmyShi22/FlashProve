-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/PaysOk.lean: the closing of a segment (K10): the tests on rows, short pieces and rounds accept at each closing. Kernel evaluations at written values; the terms are in
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
/-- The tests accept at each of the 25 closings: by Lean's kernel. -/
theorem closeOk_all : parsW.all closeOkB = true := by decide +kernel


end AtFullSide.K10

#print axioms AtFullSide.K10.closeOk_all
