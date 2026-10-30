-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Port/TwNumsO65.lean.
The public numbers of the small lookup.

One definition: `o65S := Sizes.ofPublic OnBytes.Lkp.o65`: the numbers of
OnBytes/Tie/Pv/Lookup/Port/TwNums.lean read off the value
`OnBytes.Lkp.o65` (OnBytes/Iop/LkpO65.lean), field by field; no second value is typed.
Limits: no statement. `ofPublic` does not read every field: see its docstring and `Sizes.served` in
OnBytes/Tie/Pv/Lookup/Port/TwNums.lean. At these numbers, by their shape, some things do not show:
pads = [(1, 1)], so the order of the pair and ^ against * do not show; a second table level, rows
beyond 0 and 1, and the subtraction in `keyEntry` are not exercised.

-/
import OnBytes.Tie.Pv.Lookup.Port.TwNums
import OnBytes.Iop.LkpO65

set_option autoImplicit false

namespace TwNums

/-- the small lookup's numbers: `OnBytes.Lkp.o65`, read off -/
def o65S : Sizes := Sizes.ofPublic OnBytes.Lkp.o65

end TwNums
