-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/LitCanFailFull.lean: the test of Row.lean can fail at the written records of
the full example: at each of the 25 it says no at the five altered records of LitCanFail.lean.
Evaluations in Lean's kernel, one theorem for each different record.
  full_can_fail: the test says no at each
A file of controls: no other file imports it.
Limits: written numbers; five alterations. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.LitCanFail

set_option autoImplicit false
set_option relaxedAutoImplicit false
-- Lean checks this file's theorems one after another, not side by side: as measured, the peak of
-- memory is then lower and steadier.
set_option Elab.async false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Params

set_option maxRecDepth 1000000 in
theorem full0_fails : ((altered full0).all fun x => !x.ok) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem fullOdd_fails : ((altered fullOdd).all fun x => !x.ok) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem fullEven_fails : ((altered fullEven).all fun x => !x.ok) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem full23_fails : ((altered full23).all fun x => !x.ok) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem full24_fails : ((altered full24).all fun x => !x.ok) = true := by decide +kernel

/-- The test can fail. -/
theorem full_can_fail : (tableFullLit.all fun r => (altered r).all fun x => !x.ok) = true :=
  full_all _ full0_fails fullOdd_fails fullEven_fails full23_fails full24_fails

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.full_can_fail
