-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/LitSmall.lean: the test of Row.lean says yes at each of the 5 written
records of the small example (LitRows.lean): five evaluations in Lean's kernel, a theorem each.
  small0_ok … small4_ok: the test at each record
  tableSmallLit_ok: at all 5
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
theorem small0_ok : (smallAt 0).ok = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem small1_ok : (smallAt 1).ok = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem small2_ok : (smallAt 2).ok = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem small3_ok : (smallAt 3).ok = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem small4_ok : (smallAt 4).ok = true := by decide +kernel

/-- The test says yes at each of the 5. -/
theorem tableSmallLit_ok : (tableSmallLit.all fun r => r.ok) = true :=
  small_all _ small0_ok small1_ok small2_ok small3_ok small4_ok

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.tableSmallLit_ok
