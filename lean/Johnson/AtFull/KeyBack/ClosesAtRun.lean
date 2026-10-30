-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/ClosesAtRun.lean: the key file's written declared rounds carry, at their
rounds of positions, just the lists that the rule makes of the key file's trees, at the full size. A
closed fact.

`closesB` (DeclCloser.lean) at the typed shape (`keyFull`,
Johnson/Goal/PlanValues/KeySizedReturns.lean) and the three chains' trees as terms that can be
evaluated (`runA`, `runB`, `runC`, TreesAtKey.lean). It holds two things against each other that
were made on different roads: the rule's lists (each tree's depth, width, number and source;
Johnson/G/RoundsOfPlan.lean) and the written dry lists turned back (`declKeyFull`,
Johnson/HB/LLHARD/KB8/Written.lean). By an evaluation in Lean's kernel (`decide +kernel`).

Limits. It names no m. That the written dry lists are what the program's dry runs state is not said.
That the written values are the planner's at any public files is not said. Nothing on soundness,
nothing on hiding.

-/
import Johnson.AtFull.KeyBack.DeclCloser
import Johnson.AtFull.KeyBack.TreesAtKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open Lk6.AtPlan (keyFull)

set_option maxRecDepth 1000000 in
/-- **The written declared rounds carry the rule's lists at the key file's trees.** -/
theorem closes_run : closesB keyFull.once.shape runA runB runC = true := by decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.closes_run
