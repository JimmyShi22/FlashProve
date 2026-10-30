-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/KeyFirstHasSample.lean: the written first plan of a key file of full size has an
entry for a table's own sample: the test `noSample` (Johnson/AtFull/Made/ReadsOfConfigure.lean) says
no there. One closed fact, by Lean's kernel (`decide +kernel`). It stands alone in its file because
the kernel may have to unroll the plan's 18,852 entries.

Limits. It serves no law: it shows that the test can say no at a written plan. Nothing on soundness.

-/
import Johnson.AtFull.Made.ReadsOfConfigure
import Johnson.Desc.Ok.NumberPrices.KeyAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open VerifiableInference.Number.ByRuns (keyThree)

set_option maxRecDepth 1000000 in
theorem noSample_key0_false : noSample keyThree.A.plan.plan = false := by decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.noSample_key0_false
