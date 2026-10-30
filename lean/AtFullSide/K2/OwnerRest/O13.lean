-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/OwnerRest/O13.lean: at the link 13, at the seven small pieces, by Lean's kernel.
-/
import AtFullSide.K2.OwnerRest.L13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open ProofFile.Honest ProofFile.Honest.K14
open AtFullSide.K14
open ProofFile.Honest.K2.Law (placesW)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- At the seven small pieces. -/
theorem smallW13 : ((placesW.filter fun p => p.link == 13).all fun p =>
    decide (smallPieces.map (fun l => ownerEntriesIn l p) = restO13)) = true := by
  decide +kernel

end AtFullSide.K2

#print axioms AtFullSide.K2.smallW13
