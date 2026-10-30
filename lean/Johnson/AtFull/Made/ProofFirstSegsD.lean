-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ProofFirstSegsD.lean: at the written sizes of the proof file and the written
arms, the pieces 15 to 19 of the routine of the first chain go from nothing open to nothing open:
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
theorem seg_15 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 15) () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem seg_16 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 16) () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem seg_17 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 17) () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem seg_18 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 18) () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem seg_19 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 19) () = true := by
  decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.seg_15
#print axioms Johnson.AtFull.Made.seg_16
#print axioms Johnson.AtFull.Made.seg_17
#print axioms Johnson.AtFull.Made.seg_18
#print axioms Johnson.AtFull.Made.seg_19
