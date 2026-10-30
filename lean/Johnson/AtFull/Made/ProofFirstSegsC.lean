-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ProofFirstSegsC.lean: at the written sizes of the proof file and the written
arms, the pieces 10 to 14 of the routine of the first chain go from nothing open to nothing open:
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
theorem seg_10 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 10) () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem seg_11 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 11) () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem seg_12 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 12) () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem seg_13 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 13) () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem seg_14 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 14) () = true := by
  decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.seg_10
#print axioms Johnson.AtFull.Made.seg_11
#print axioms Johnson.AtFull.Made.seg_12
#print axioms Johnson.AtFull.Made.seg_13
#print axioms Johnson.AtFull.Made.seg_14
