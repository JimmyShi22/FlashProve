-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/ArmsAtMakersNo.lean: TWO NEGATIVE TESTS OF `arms_W`
(Johnson/AtFull/Public/ArmsAtMakers.lean), by Lean's kernel, each stated as "the makers return, and
the test rejects" (so that a maker's refusal would not pass for a rejection): with
the layers' plans in reversed order layersB says no; with the attention's plans in reversed order
attB says no. At which clause each says no is not shown. A control on the order of the groups alone:
the clauses that are one number for all groups, and the clause on the size, are not tried. It is
imported by nothing. Nothing on soundness.
-/
import Johnson.AtFull.Public.AtWitnesses

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Public

theorem layers_no : atMakers (fun L G _ => !layersB L G.reverse) = true := by decide +kernel

theorem att_no : atMakers (fun _ _ A => !attB A.reverse) = true := by decide +kernel

end Johnson.AtFull.Public

#print axioms Johnson.AtFull.Public.layers_no
#print axioms Johnson.AtFull.Public.att_no
