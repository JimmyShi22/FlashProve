-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/OwnerRest/T17.lean: at the link 17, the test says yes at the whole, by Lean's kernel.
-/
import AtFullSide.K2.OwnerRest.L17

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open ProofFile.Honest ProofFile.Honest.K14
open AtFullSide.K14
open ProofFile.Honest.K2.Law (placesW)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test says yes at the whole. -/
theorem ownerRestW17 : ((placesW.filter fun p => p.link == 17).all fun p =>
    restTest p (joinPieces restA17 restS17 restO17)) = true := by
  decide +kernel

end AtFullSide.K2

#print axioms AtFullSide.K2.ownerRestW17
