-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5FrontSame.lean: THE WALKER SAYS YES AT THE TWO WRITTEN LISTS' RUNS
(`sameRunsB`, K5FrontRuns.lean; `runsA` · `runsD`, K5FrontSameDefs.lean). One decision of Lean's
kernel: some 34 thousand steps, each an equality of a name and eleven numbers.
Limits. The full size alone. A closed fact. Nothing on soundness. On hiding nothing.

-/
import Johnson.Desc.First.Att.Row.K5FrontSameDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row

set_option maxRecDepth 1000000 in
/-- **The walker says yes.** -/
theorem same_written : sameRunsB 40000 runsA runsD = true := by decide +kernel

end H2K5.Row

#print axioms H2K5.Row.same_written
