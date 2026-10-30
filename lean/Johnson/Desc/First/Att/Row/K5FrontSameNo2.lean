-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5FrontSameNo2.lean: A SECOND NEGATIVE TEST TO `same_written`
(K5FrontSame.lean): with one entry more IN THE MIDDLE of the dry runs' list (a further copy of run
number 9,000's entry, laid in front of that run) the walker says no: the comparison of entries
bites.
One decision of Lean's kernel, stated positively.
Limits. One fault at one place. The full size alone. Nothing on soundness. On hiding nothing.

-/
import Johnson.Desc.First.Att.Row.K5FrontSameDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row

set_option maxRecDepth 1000000 in
/-- **With one entry more in the middle the walker says no.** -/
theorem same_refuses_mid :
    sameRunsB 40000 runsA
      (runsD.take 9000 ++ (1, (runsD.getD 9000 (0, default)).2) :: runsD.drop 9000) = false := by
  decide +kernel

end H2K5.Row

#print axioms H2K5.Row.same_refuses_mid
