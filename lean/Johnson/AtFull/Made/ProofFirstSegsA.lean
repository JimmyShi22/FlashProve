-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ProofFirstSegsA.lean: at the written sizes of the proof file and the written
arms, the pieces 0 to 4 of the routine of the first chain go from nothing open to nothing open:
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
theorem seg_0 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 0) () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem seg_1 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 1) () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem seg_2 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 2) () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem seg_3 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 3) () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem seg_4 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 4) () = true := by
  decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.seg_0
#print axioms Johnson.AtFull.Made.seg_1
#print axioms Johnson.AtFull.Made.seg_2
#print axioms Johnson.AtFull.Made.seg_3
#print axioms Johnson.AtFull.Made.seg_4
