-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ProofFirstSegsE.lean: at the written sizes of the proof file and the written
arms, the pieces 20 to 24 of the routine of the first chain, the piece without a link and what
follows the frame go from nothing open to nothing open: closed facts, each by an evaluation in
Lean's kernel (`decide +kernel`) of the test `goesB` (Johnson/AtFull/Made/Goes.lean) at a piece
(`segAt`, `lastAt`, `tailOf`: Johnson/AtFull/Made/FirstCut.lean). A law file; no running text
imports it. Laid by a program: one statement a piece.

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
theorem seg_20 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 20) () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem seg_21 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 21) () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem seg_22 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 22) () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem seg_23 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 23) () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem seg_24 :
    goesB proofSizedFull.set
      (segAt proofSizedFull subW (reqGroups proofSizedFull.request).toList 24) () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem last_25 :
    goesB proofSizedFull.set
      (lastAt proofSizedFull (reqGroups proofSizedFull.request).toList 25) () = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem tail_goes : goesB proofSizedFull.set (tailOf proofSizedFull subW) () = true := by
  decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.seg_20
#print axioms Johnson.AtFull.Made.seg_21
#print axioms Johnson.AtFull.Made.seg_22
#print axioms Johnson.AtFull.Made.seg_23
#print axioms Johnson.AtFull.Made.seg_24
#print axioms Johnson.AtFull.Made.last_25
#print axioms Johnson.AtFull.Made.tail_goes
