-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/K3X/KernelLayersNo.lean: THREE NEGATIVE TESTS OF layers_W
(Johnson/AtFull/K3X/KernelLayers.lean), by evaluation in Lean's kernel, each stated as "the makers
return twelve plans, and the test rejects" (so that neither a maker's refusal nor an empty list of
plans would pass for a rejection): with the plans in reversed order; with the shape's limit on a
tree's depth raised by one; with the depth of a tree of the lookup on the digits raised by one in
every plan. At which clause each rejects is not shown. What follows is a reading of the test's text,
no theorem (a plain conjunction; each change touches one field; layers_W holds the other clauses
true): reversed order: the number of slots, which is 4059 at group 0 and 4058 at the eleven others,
and the first slot of the lookup on the digits with it: so it tells group 0 from the others alone;
the limit: the comparison with 28; the depth: of the clauses on the digits the host's count alone
reads it: whether that count returns nothing or another list is not shown.
Limits. All three changes are laid on the made values, behind the makers: they try the test's text,
not the makers. MOST CLAUSES OF layersT HAVE NO NEGATIVE TEST OF THEIR OWN: the eight calls, the
second number of the shape, the first free slot, the number of slots at groups 1 to 11; of the
digits the two calls, the counts, the depth limit, the test on the padding key. It is imported by
nothing. Nothing on soundness.

-/
import Johnson.AtFull.K3X.KernelTests
import Johnson.AtFull.Public.AtWitnesses

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.K3X
open Johnson.AtFull.Public (atMakers)

theorem layers_no_order : atMakers (fun L G _ => G.size == 12 && !layersT L G.reverse) = true := by
  decide +kernel

theorem layers_no_limit : atMakers (fun L G _ => G.size == 12 &&
    !layersT { L with y := { L.y with h := { L.y.h with lidb := L.y.h.lidb + 1 } } } G) = true := by
  decide +kernel

theorem layers_no_depth : atMakers (fun L G _ => G.size == 12 && !layersT L (G.map fun hp =>
    { hp with tl := { hp.tl with f9 := { hp.tl.f9 with dT := hp.tl.f9.dT + 1 } } })) = true := by
  decide +kernel

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.layers_no_order
#print axioms Johnson.AtFull.K3X.layers_no_limit
#print axioms Johnson.AtFull.K3X.layers_no_depth
