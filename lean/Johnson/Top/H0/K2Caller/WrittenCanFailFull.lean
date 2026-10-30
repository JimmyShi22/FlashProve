-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/WrittenCanFailFull.lean: the test `SwRow.writtenOK` of WrittenMeets.lean can
fail at the written records of the full example: at each of the 25 it says no at the three altered
records of WrittenCanFail.lean. Evaluations in Lean's kernel, one theorem for each different record.
  full_written_can_fail: the test says no at each
A file of controls: no other file imports it.
Limits: written numbers; three alterations; which clause of the test says no at an altered record is
not said. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.WrittenCanFail

set_option autoImplicit false
set_option relaxedAutoImplicit false
-- Lean checks this file's theorems one after another, not side by side: as measured, the peak of
-- memory is then lower and steadier.
set_option Elab.async false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Params

set_option maxRecDepth 1000000 in
theorem full0_wfails : ((alteredW full0).all fun x => !x.writtenOK) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem fullOdd_wfails : ((alteredW fullOdd).all fun x => !x.writtenOK) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem fullEven_wfails :
    ((alteredW fullEven).all fun x => !x.writtenOK) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem full23_wfails : ((alteredW full23).all fun x => !x.writtenOK) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem full24_wfails : ((alteredW full24).all fun x => !x.writtenOK) = true := by decide +kernel

/-- The test can fail. -/
theorem full_written_can_fail :
    (tableFullLit.all fun r => (alteredW r).all fun x => !x.writtenOK) = true :=
  full_all _ full0_wfails fullOdd_wfails fullEven_wfails full23_wfails full24_wfails

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.full_written_can_fail
