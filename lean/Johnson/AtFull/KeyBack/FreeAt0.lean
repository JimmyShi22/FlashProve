-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/FreeAt0.lean: ONE CLOSED FACT: the 18805 rounds in front of the first "BAT"
of the key file's first written plan receive two roots. By an evaluation in Lean's kernel (`decide
+kernel`).
Limits. A closed fact on written files: it names no m and no public file. That a planner's answer
holds these written plans or sizes is not said here. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.KPlans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open OnBytes OnBytes.Params

set_option maxRecDepth 1000000 in
/-- The roots in front. -/
theorem free_A : ((roundsA.take 18805).map (·.roots)).foldl (· + ·) 0 = 2 := by decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.free_A
