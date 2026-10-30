-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/K3X/KernelAtt.lean: THE CLOSED FACT ON THE ATTENTION's TWELVE LINKS, proved by
evaluation in Lean's kernel, no free letter: at what the public part's makers return at the full
size (atMakers, Johnson/AtFull/Public/AtWitnesses.lean; the attention's groups by their twins), the
test attT (Johnson/AtFull/K3X/KernelTests.lean) accepts: at each of twelve groups the plan's four
calls with their tables taken out, its eleven counts of padding keys, four numbers, the host's own
count, and all that the lookup on the digits reads, are the written ones.
Negative tests stand beside it: Johnson/AtFull/K3X/KernelAttNo.lean.

Limits. At the makers' twins and the written scan: the tie to the public part's own value is
at_witnesses'. The test on the padding key of the lookup on the calls is not here: a law pays it
(Johnson/AtFull/K3X/PadKeyLaw.lean). Nothing on soundness.

-/
import Johnson.AtFull.K3X.KernelTests
import Johnson.AtFull.Public.AtWitnesses

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.K3X
open Johnson.AtFull.Public (atMakers)

theorem att_W : atMakers (fun _ _ A => attT A) = true := by decide +kernel

end Johnson.AtFull.K3X

#print axioms Johnson.AtFull.K3X.att_W
