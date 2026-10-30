-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/LevelFull.lean: the planner's test on the level (SwRow.levelOK,
LevelDef.lean) says yes at each of the 25 written records of the full example, and there the target
is 128 and the two rounds' bits of work are 0 and 20: evaluations in Lean's kernel, one at each
different record, a theorem each.
  full_level_ok: the test says yes at each
  full_works: the target and the two numbers of bits at each
Limits: those of LevelDef.lean and LitRows.lean. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.LevelDef
import Johnson.Top.H0.K2Caller.LitRows

set_option autoImplicit false
set_option relaxedAutoImplicit false
-- Lean checks this file's theorems one after another, not side by side: as measured, the peak of
-- memory is then lower and steadier.
set_option Elab.async false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Params

set_option maxRecDepth 1000000 in
theorem full0_level : full0.levelOK = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem fullOdd_level : fullOdd.levelOK = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem fullEven_level : fullEven.levelOK = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem full23_level : full23.levelOK = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem full24_level : full24.levelOK = true := by decide +kernel

theorem full_level_ok : (tableFullLit.all fun r => r.levelOK) = true :=
  full_all _ full0_level fullOdd_level fullEven_level full23_level full24_level

set_option maxRecDepth 1000000 in
theorem full0_works : decide (full0.works = (128, [0, 20])) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem fullOdd_works : decide (fullOdd.works = (128, [0, 20])) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem fullEven_works : decide (fullEven.works = (128, [0, 20])) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem full23_works : decide (full23.works = (128, [0, 20])) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem full24_works : decide (full24.works = (128, [0, 20])) = true := by decide +kernel

theorem full_works : (tableFullLit.all fun r => decide (r.works = (128, [0, 20]))) = true :=
  full_all _ full0_works fullOdd_works fullEven_works full23_works full24_works

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.full_level_ok
#print axioms VerifiableInference.Desc.First.K2Caller.full_works
