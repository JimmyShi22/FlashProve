-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/K3X/KernelLayers.lean: THE CLOSED FACT ON THE LAYERS' TWELVE LINKS, proved by
evaluation in Lean's kernel, no free letter: at what the public part's makers return at the full
size (atMakers, Johnson/AtFull/Public/AtWitnesses.lean), the test layersT
(Johnson/AtFull/K3X/KernelTests.lean) accepts: the eight calls with their tables taken out and two
numbers of the shape are the written ones; at each of twelve groups the plan's first free slot and
number of slots, and all that the lookup on the digits reads, are the written ones.
Negative tests stand beside it: Johnson/AtFull/K3X/KernelLayersNo.lean.

Limits. At the makers' twins and the written scan: the tie to the public part's own value is
at_witnesses'. The test reads neither the layers' sixteen counts of padding keys nor the host's
count at the lookup on the calls: these are paid by laws. Nothing on soundness.

-/
import Johnson.AtFull.K3X.KernelTests
import Johnson.AtFull.Public.AtWitnesses

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.K3X
open Johnson.AtFull.Public (atMakers)

theorem layers_W : atMakers (fun L G _ => layersT L G) = true := by decide +kernel

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.layers_W
