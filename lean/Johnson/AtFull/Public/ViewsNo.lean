-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/ViewsNo.lean: A NEGATIVE TEST OF `views24_W`
(Johnson/AtFull/Public/Views.lean): held against the written list less its first member (24 members
too: every view meets its neighbour's), the same comparison says no. By Lean's kernel. Stated as
"the makers return, and the comparison rejects" (so that a maker's refusal would not pass for a
rejection), in the form of `viewsAt_eq` (Johnson/AtFull/Public/AtWitnesses.lean). What it is worth:
it shows that the makers return and that the comparison can say no. Beside `views24_W` it comes down
to this: the written list's first 24 members are not its last 24, and these two lists part at the
first member's name already; no other field is tried. It is imported by nothing. Nothing on
soundness.
-/
import Johnson.AtFull.Public.AtWitnesses

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Public

open Johnson.AtFull.Made.Decl (viewsFull)

/-- The makers return, and the comparison rejects a list that is not the makers'. -/
theorem views24_no :
    atMakers (fun _ G A => !decide (viewsBefore G A = viewsFull.drop 1)) = true := by
  decide +kernel

end Johnson.AtFull.Public

#print axioms Johnson.AtFull.Public.views24_no
