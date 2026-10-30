-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/LitFull.lean: the test of Row.lean says yes at each of the 25 written
records of the full example (LitRows.lean): five evaluations in Lean's kernel, one at each different
record, a theorem each.
  full0_ok, fullOdd_ok, fullEven_ok, full23_ok, full24_ok: the test at each different record
  tableFullLit_ok: at all 25, by full_all
Limits: those of LitRows.lean and Row.lean. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.LitRows

set_option autoImplicit false
set_option relaxedAutoImplicit false
-- Lean checks this file's theorems one after another, not side by side: as measured, the peak of
-- memory is then lower and steadier.
set_option Elab.async false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Params

set_option maxRecDepth 1000000 in
theorem full0_ok : full0.ok = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem fullOdd_ok : fullOdd.ok = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem fullEven_ok : fullEven.ok = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem full23_ok : full23.ok = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem full24_ok : full24.ok = true := by decide +kernel

/-- The test says yes at each of the 25. -/
theorem tableFullLit_ok : (tableFullLit.all fun r => r.ok) = true :=
  full_all _ full0_ok fullOdd_ok fullEven_ok full23_ok full24_ok

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.tableFullLit_ok
