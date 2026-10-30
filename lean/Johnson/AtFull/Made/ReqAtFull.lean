-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ReqAtFull.lean: the written shape of a request at the full size passes the test
under which it is read back as it was spelled.

The shape is `proofSizedFull.request` (Johnson/Desc/Ok/PlanWritten/SizedLit.lean), the test `reqB`
(Johnson/AtFull/Made/ItemTests.lean). Closed facts, by Lean's kernel (`decide +kernel`). The test
reads numbers: no byte is laid.

Limits. That the written shape is what the planner makes is not said here. Nothing on soundness.

-/
import Johnson.AtFull.Made.ItemTests
import Johnson.Desc.Ok.PlanWritten.SizedLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten (proofSizedFull)

set_option maxRecDepth 1000000 in
theorem reqB_proofFull : reqB proofSizedFull.request = true := by decide +kernel

/-- An oracle message of a link with nine main rows, no mask rows and one answer. -/
def plainMessage (deg maskCode life : Nat) : ReqMessage :=
  ⟨⟨0, 9, deg, 0, maskCode, 1⟩, 0, 0, life⟩

/-- The written shape with a first link that has the one message m. -/
def withFirst (m : ReqMessage) : ReqShape :=
  { proofSizedFull.request with link := ⟨0, [m]⟩ :: proofSizedFull.request.link.drop 1 }

set_option maxRecDepth 1000000 in
/-- With a first link whose one message is in order the shape still passes. So each of the three
negative tests below that change this message fails for what it changes. -/
theorem reqB_withFirst : reqB (withFirst (plainMessage 1 noId 0)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Negative tests: no stage of the last test; another number of answers than the messages have;
another first stage; a message without mask rows and with the mask code 0; a message that is kept
beyond the last link; a message of degree 2; a notice at the start without mask rows and with the
mask code 0. -/
theorem reqB_rejects :
    (reqB { proofSizedFull.request with last := [] },
      reqB { proofSizedFull.request with answers := proofSizedFull.request.answers + 1 },
      reqB { proofSizedFull.request with
        last := ⟨0, 0, 2, 0⟩ :: proofSizedFull.request.last.drop 1 },
      reqB (withFirst (plainMessage 1 0 0)),
      reqB (withFirst (plainMessage 1 noId 25)),
      reqB (withFirst (plainMessage 2 noId 0)),
      reqB { proofSizedFull.request with atStart := [⟨⟨0, 9, 1, 0, 0, 1⟩, 0⟩] }) =
      (false, false, false, false, false, false, false) := by decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.reqB_proofFull
#print axioms Johnson.AtFull.Made.reqB_withFirst
#print axioms Johnson.AtFull.Made.reqB_rejects
