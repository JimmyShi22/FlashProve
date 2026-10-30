-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ProofFirstSegsB.lean: at the written sizes of the proof file and the written
arms, the pieces 5 to 9 of the routine of the first chain go from nothing open to nothing open:
closed facts, each by an evaluation in Lean's kernel (`decide +kernel`) of the test `goesB`
(Johnson/AtFull/Made/Goes.lean) at a piece (`segAt`, `lastAt`, `tailOf`:
Johnson/AtFull/Made/FirstCut.lean). A law file; no running text imports it. Laid by a program: one
statement a piece.

Limits. A yes says that the piece returns from the plan without rounds, not what it adds. That the
written sizes and arms are those of any public files is not said here. Nothing on soundness.

-/
import Johnson.AtFull.Made.FirstCut
import Johnson.AtFull.Made.ArmList
import Johnson.Desc.Ok.PlanWritten.SizedLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten (proofSizedFull)

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem seg_5 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 5) () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem seg_6 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 6) () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem seg_7 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 7) () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem seg_8 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 8) () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem seg_9 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 9) () = true := by
  decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.seg_5
#print axioms Johnson.AtFull.Made.seg_6
#print axioms Johnson.AtFull.Made.seg_7
#print axioms Johnson.AtFull.Made.seg_8
#print axioms Johnson.AtFull.Made.seg_9
