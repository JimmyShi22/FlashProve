-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ProofItemsAtFull.lean: at the written sizes of a proof file of full size, the
codes, the shape of the test on the table, the number of pending rows and the shape of the binding
tree pass the tests under which they are read back as they were spelled.

The written sizes are `proofSizedFull` (Johnson/Desc/Ok/PlanWritten/SizedLit.lean); 13 and ⟨6, 40⟩
are the numbers of `FirstWritten` (Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean). The tests are in
Johnson/HB/LLHARD/KB9/ItemsOk.lean. Closed facts, by Lean's kernel (`decide +kernel`). The tests
read numbers: no byte is laid.

Limits. That the written sizes are what the planner makes is not said here. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB9.ItemsOk
import Johnson.Desc.Ok.PlanWritten.SizedLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open Johnson.KB9 (wB codesB linB bindingB)
open VerifiableInference.PlanWritten (proofSizedFull)

set_option maxRecDepth 1000000 in
theorem codesB_proofFull : codesB proofSizedFull.codes = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem linB_proofFull : linB proofSizedFull.batch.shape = true := by decide +kernel

theorem wB_thirteen : wB 13 = true := by decide +kernel

theorem bindingB_six_forty : bindingB ⟨6, 40⟩ = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Negative tests: a code's length of 2 ^ 64; a shape without mask rows whose mask code is 0. -/
theorem proofItems_rejects :
    (codesB { proofSizedFull.codes with base := #[⟨2 ^ 64, 0, 0⟩] },
      linB { proofSizedFull.batch.shape with
        omega := { proofSizedFull.batch.shape.omega with maskRows := 0, maskCode := 0 } },
      wB (2 ^ 64), bindingB ⟨6, 2 ^ 64⟩) = (false, false, false, false) := by decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.codesB_proofFull
#print axioms Johnson.AtFull.Made.linB_proofFull
#print axioms Johnson.AtFull.Made.wB_thirteen
#print axioms Johnson.AtFull.Made.bindingB_six_forty
#print axioms Johnson.AtFull.Made.proofItems_rejects
