-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/FillsAtRun.lean: the seven tests behind `declKOf` say yes at the key file's
written plans, typed shape and trees, at the full size. A closed fact.

`fillsB` (FillsBool.lean) at the three numbers of rounds that draw positions (4, 10, 5:
DrawsAt0.lean, DrawsAt1.lean, DrawsAt2.lean), the typed shape (`keyFull`,
Johnson/Goal/PlanValues/KeySizedReturns.lean) and the three chains' trees as terms that can be
evaluated (`runA`, `runB`, `runC`, TreesAtKey.lean). By an evaluation in Lean's kernel (`decide
+kernel`).

Limits. It names no m: that any m has these plans, this shape and these trees is not said here. That
the written values are the planner's at any public files is not said.
Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.FillsBool
import Johnson.AtFull.KeyBack.TreesAtKey
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open Lk6.AtPlan (keyFull)

set_option maxRecDepth 1000000 in
/-- **The seven tests say yes at the key file's trees.** -/
theorem fills_run : fillsB 4 10 5 keyFull.once.shape runA runB runC = true := by decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.fills_run
