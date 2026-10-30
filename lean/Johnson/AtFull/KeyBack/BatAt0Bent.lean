-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/BatAt0Bent.lean: A CONTROL OF BatAt0.lean: at the very term of `bat_first_A`
the kernel's evaluation comes out the other way at a bent value. By an evaluation in Lean's kernel
(`decide +kernel`). It follows from `bat_first_A` too, and adds nothing to it: it shows that the
decision can say no.
Limits. A closed fact on written files: it names no m and no public file. That a planner's answer
holds these written plans or sizes is not said here. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.KPlans
import Johnson.Desc.K12.Plan.TestCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params

set_option maxRecDepth 1000000 in
/-- The first "BAT" does not stand at 18804. -/
theorem bat_first_A_bent : ¬ (H2U.batPlaces roundsA).head? = some 18804 := by decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.bat_first_A_bent
