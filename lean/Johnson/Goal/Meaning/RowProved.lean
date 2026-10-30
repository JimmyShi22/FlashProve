-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RowProved.lean: the row on the meaning (TieRow, Johnson/Goal/Meaning/Row.lean)
as a theorem: tieRow_of at layersSay (Johnson/Goal/Meaning/LayersSay.lean). What it says, what it
rests on and what it does not claim: the head of Johnson/Goal/Meaning/Row.lean.
-/
import Johnson.Goal.Meaning.Row
import Johnson.Goal.Meaning.LayersSay

set_option autoImplicit false

namespace Meaning

/-- **THE ROW.** -/
theorem tieRow : TieRow := tieRow_of layersSay

end Meaning

#print axioms Meaning.tieRow
