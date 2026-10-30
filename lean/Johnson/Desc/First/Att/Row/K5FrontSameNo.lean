-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5FrontSameNo.lean: A NEGATIVE TEST TO `same_written` (K5FrontSame.lean):
with
one entry more at the end of the dry runs' list the walker says no: it walks all the runs first.
One decision of Lean's kernel, stated positively.
Limits. One fault at one place. The full size alone. Nothing on soundness. On hiding nothing.

-/
import Johnson.Desc.First.Att.Row.K5FrontSameDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row

set_option maxRecDepth 1000000 in
/-- **With one entry more at the end the walker says no.** -/
theorem same_refuses :
    sameRunsB 40000 runsA (runsD ++ [(1, (runsD.getLastD (0, default)).2)]) = false := by
  decide +kernel

end H2K5.Row

#print axioms H2K5.Row.same_refuses
