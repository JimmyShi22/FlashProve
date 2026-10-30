-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5OwnPlanOk.lean: AT THE WRITTEN NUMBERS (`ownW`, K5OwnW.lean) KIND K5's
TEST ON THE PLAN's OWN
NUMBERS SAYS YES. One small decision of Lean's kernel.
Limits. The full size alone. A WRITTEN value. Nothing on soundness. On hiding nothing.

-/
import Johnson.Desc.First.Att.Row.K5OwnW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row

theorem planOk_written : planOkOwn ownW = true := by decide +kernel

end H2K5.Row

#print axioms H2K5.Row.planOk_written
