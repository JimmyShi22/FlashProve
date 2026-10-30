-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/ClosesAtRunBent.lean: `closes_run` (ClosesAtRun.lean) with a value bent. A
test of the test.

`closes_run_bent`: the last of the first chain's trees, W's, is left out. The test says no. By a
reading of its text, which no theorem here says, for two reasons: the second chain's first list
lacks a tree that is taken over, and the second chain's own trees are numbered from one less.
By an evaluation in Lean's kernel (`decide +kernel`).
Limits. Nothing follows from it for any key file. Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.ClosesAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open Lk6.AtPlan (keyFull)

set_option maxRecDepth 1000000 in
/-- W's tree left out of the first chain's trees: the test says no. -/
theorem closes_run_bent : closesB keyFull.once.shape runA.dropLast runB runC = false := by
  decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.closes_run_bent
