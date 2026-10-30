-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5BeforeClosedNo.lean: kind K5's row: THE NEGATIVE TWIN of before_closed
(Johnson/Desc/First/Att/Row/K5BeforeClosed.lean): the same test says NO where one number of the
twelve is bent (at the last segment 71 for 70): so the test can fail, and its yes is no stuck
term's. ONE DECISION, ALONE IN ITS MODULE.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Row.K5BeforeClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test refuses a bent column. -/
theorem before_closed_no : beforeAllB (fun g => if g = 11 then [(1, 71)] else [(1, 4 + 6 * g)]) = false := by decide +kernel

end H2K5.Row

#print axioms H2K5.Row.before_closed_no
