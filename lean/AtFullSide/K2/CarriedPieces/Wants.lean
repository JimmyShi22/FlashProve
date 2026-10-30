-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/CarriedPieces/Wants.lean: by Lean's kernel, the book's stretches carry nothing to the code switch's parts.
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
theorem wantsKept_none : (rawWantsW.map (·.entry)).filter keepK2 = [] := by
  decide +kernel

end AtFullSide.K2

#print axioms AtFullSide.K2.wantsKept_none
