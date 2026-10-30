-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/FreeAt0Bent.lean: A CONTROL OF FreeAt0.lean: at the very term of `free_A` the
kernel's evaluation comes out the other way at a bent value. By an evaluation in Lean's kernel
(`decide +kernel`). It follows from `free_A` too, and adds nothing to it: it shows that the decision
can say no.
Limits. A closed fact on written files: it names no m and no public file. That a planner's answer
holds these written plans or sizes is not said here. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.KPlans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params

set_option maxRecDepth 1000000 in
/-- The roots in front are not 3. -/
theorem free_A_bent : ¬ ((roundsA.take 18805).map (·.roots)).foldl (· + ·) 0 = 3 := by
  decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.free_A_bent
