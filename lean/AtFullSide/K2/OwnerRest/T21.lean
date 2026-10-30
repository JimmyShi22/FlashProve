-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/OwnerRest/T21.lean: at the link 21, the test says yes at the whole, by Lean's kernel.
-/
import AtFullSide.K2.OwnerRest.L21

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open ProofFile.Honest ProofFile.Honest.K14
open AtFullSide.K14
open ProofFile.Honest.K2.Law (placesW)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test says yes at the whole. -/
theorem ownerRestW21 : ((placesW.filter fun p => p.link == 21).all fun p =>
    restTest p (joinPieces restA21 restS21 restO21)) = true := by
  decide +kernel

end AtFullSide.K2

#print axioms AtFullSide.K2.ownerRestW21
