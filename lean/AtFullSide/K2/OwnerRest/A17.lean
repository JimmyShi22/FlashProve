-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/OwnerRest/A17.lean: at the link 17, at the book's stretches, by Lean's kernel.
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
/-- At the stretches. -/
theorem wantsW17 : ((placesW.filter fun p => p.link == 17).all fun p =>
    decide (ownerEntriesIn (rawWantsW.map (·.entry)) p = restA17)) = true := by
  decide +kernel

end AtFullSide.K2

#print axioms AtFullSide.K2.wantsW17
