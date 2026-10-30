-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/WrittenLitFull.lean: the test SwRow.writtenOK of WrittenMeets.lean says yes
at each of the 25 written records of the full example: evaluations in Lean's kernel, one at each
different record, a theorem each.
  full_written_ok: the test says yes at each
Limits: written numbers. Those of WrittenMeets.lean. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.WrittenMeets

set_option autoImplicit false
set_option relaxedAutoImplicit false
-- Lean checks this file's theorems one after another, not side by side: as measured, the peak of
-- memory is then lower and steadier.
set_option Elab.async false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Params

set_option maxRecDepth 1000000 in
theorem full0_written : full0.writtenOK = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem fullOdd_written : fullOdd.writtenOK = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem fullEven_written : fullEven.writtenOK = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem full23_written : full23.writtenOK = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem full24_written : full24.writtenOK = true := by decide +kernel

theorem full_written_ok : (tableFullLit.all fun r => r.writtenOK) = true :=
  full_all _ full0_written fullOdd_written fullEven_written full23_written full24_written

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.full_written_ok
