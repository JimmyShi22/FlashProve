-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLBookLinePlaces.lean

It states no goal. No property of the protocol is claimed.

Two closed lines on written places.

  `closingPlaces_in_written_chain`        the closing proximity test's place and the last code switch's
                                          stand in the written first chain
  `finish_place_and_stretches_written`    the written finish stands at ⟨1, none, 1, K2⟩ and carries 184
                                          stretches

Limits. Facts on written values (WP's own limit stands). The full size alone. Nothing on completeness,
soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLOwedAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open P2Law.ProofPlan (WP)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The closing test's place and the last switch's stand in the written first chain. -/
theorem closingPlaces_in_written_chain :
    ((WP.first.blocksInOrder.map (·.place)).contains ⟨1, none, 2, .K12⟩ &&
      (WP.first.blocksInOrder.map (·.place)).contains ⟨1, none, 1, .K2⟩) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The written finish stands at ⟨1, none, 1, K2⟩ and carries 184 stretches. -/
theorem finish_place_and_stretches_written :
    finishW.map (fun p => (p.place, p.front.length)) = some (⟨1, none, 1, .K2⟩, 184) := by
  decide +kernel

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.closingPlaces_in_written_chain
#print axioms ProofFile.Honest.K12.AtProof.finish_place_and_stretches_written
