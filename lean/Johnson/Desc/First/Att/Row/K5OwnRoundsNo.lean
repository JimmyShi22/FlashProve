-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5OwnRoundsNo.lean: A NEGATIVE TEST TO `rounds_written`
(K5OwnRounds.lean): with one number bent
(lt 11 for 10) the rounds are not 162. One small decision of Lean's kernel, stated positively.
Limits. One bent number. Nothing on soundness. On hiding nothing.

-/
import Johnson.Desc.First.Att.Row.K5OwnW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row

theorem rounds_bent : (nRounds { ownW with lt := 11 } == 162) = false := by decide +kernel

end H2K5.Row

#print axioms H2K5.Row.rounds_bent
