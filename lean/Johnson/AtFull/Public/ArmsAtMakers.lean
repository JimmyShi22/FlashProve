-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/ArmsAtMakers.lean: THE CLOSED FACT THAT armsB_at
(Johnson/AtFull/Public/AtWitnesses.lean) TAKES, BY LEAN's KERNEL, no free letter: at what the public
part's makers return at the full size (the attention's groups by their twins), the tests layersB and
attB accept: twelve layers' plans and twelve attention's plans; at each group the parts that an arm
reads are the written numbers of Johnson/AtFull/Rows/ArmsOfFields.lean; the views of the 24
smallness tests are xShapeFull's segments 0 to 23 (Johnson/G/XShapeLit.lean).
A negative test stands beside it: Johnson/AtFull/Public/ArmsAtMakersNo.lean.

Limits. At the makers' twins and the written scan: the tie to the public part's own value is
at_witnesses'. The head's arm and segment 24 are not here. Nothing on soundness.

-/
import Johnson.AtFull.Public.AtWitnesses

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Public

/-- **The 24 arms and the 24 views of the smallness tests are the written ones.** -/
theorem arms_W : atMakers (fun L G A => layersB L G && attB A) = true := by decide +kernel

end Johnson.AtFull.Public

#print axioms Johnson.AtFull.Public.arms_W
