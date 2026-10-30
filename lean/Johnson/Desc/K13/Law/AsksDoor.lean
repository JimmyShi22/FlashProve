-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/AsksDoor.lean: ONE FILLING OF THE DOOR of the table of joints (`First.More`,
Johnson/Desc/First/Borders.lean): kind K13's block and W's commitment ASK the public item
"K12.seatsCarried", which K12's files lay. A definition; no theorem. It imports the table alone.
Why. The laws of these two blocks spend that item. Written as an ask in a row, the table's own
test on a filling (`First.pubFit`) guards that it is open there. Alone this filling fails that
test (asked, and made by nobody): it is merged where the filling that makes the item is merged too.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc.First (More)

/-- K13's block and W's commitment ask the item. -/
def k13Asks : More where
  rows := fun _ p =>
    if p.link.isNone && (p.kind == .K13 || p.kind == .K1) then
      { asks := [(none, "K12.seatsCarried")] }
    else {}

end VerifiableInference.Desc.K13.Law
