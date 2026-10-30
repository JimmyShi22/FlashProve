-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5OwnPlanOkNo.lean: A NEGATIVE TEST TO `planOk_written`
(K5OwnPlanOk.lean): with no pair (pairs 0 for
20) the test says no. One small decision of Lean's kernel, stated positively.
Limits. One bent number. Nothing on soundness. On hiding nothing.

-/
import Johnson.Desc.First.Att.Row.K5OwnW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row

theorem planOk_bent : planOkOwn { ownW with pairs := 0 } = false := by decide +kernel

end H2K5.Row

#print axioms H2K5.Row.planOk_bent
