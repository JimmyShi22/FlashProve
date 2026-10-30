-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/LevelSmall.lean: the planner's test on the level (SwRow.levelOK,
LevelDef.lean) says yes at each of the 5 written records of the small example, and there the target
is 128 and the two rounds' bits of work are 0 and 20: evaluations in Lean's kernel, one at each
different record, a theorem each.
  small_level_ok: the test says yes at each
  small_works: the target and the two numbers of bits at each
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
theorem small0_level : (smallAt 0).levelOK = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem small1_level : (smallAt 1).levelOK = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem small2_level : (smallAt 2).levelOK = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem small3_level : (smallAt 3).levelOK = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem small4_level : (smallAt 4).levelOK = true := by decide +kernel

theorem small_level_ok : (tableSmallLit.all fun r => r.levelOK) = true :=
  small_all _ small0_level small1_level small2_level small3_level small4_level

set_option maxRecDepth 1000000 in
theorem small0_works : decide ((smallAt 0).works = (128, [0, 20])) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem small1_works : decide ((smallAt 1).works = (128, [0, 20])) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem small2_works : decide ((smallAt 2).works = (128, [0, 20])) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem small3_works : decide ((smallAt 3).works = (128, [0, 20])) = true := by decide +kernel
set_option maxRecDepth 1000000 in
theorem small4_works : decide ((smallAt 4).works = (128, [0, 20])) = true := by decide +kernel

theorem small_works : (tableSmallLit.all fun r => decide (r.works = (128, [0, 20]))) = true :=
  small_all _ small0_works small1_works small2_works small3_works small4_works

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.small_level_ok
#print axioms VerifiableInference.Desc.First.K2Caller.small_works
