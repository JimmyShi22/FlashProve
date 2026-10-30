-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/ScalarsOnKey.lean: the count over the plain list of the key file's lookups at
the written sizes. One theorem, alone in its file.

Why. It is piece (C) of "the lookups' count returns 34,933" (`hs` of `gate_ranges_of`,
Johnson/AtFull/Made/GateRanges.lean): see ScalarsLaw.lean.

What is said. `scalars_on_key`: `scalarsOn writtenSized.key.set (lookupsList writtenSized.key) =
34933`: by an evaluation in Lean's kernel.

Limits. The written sizes alone. Nothing on soundness.
-/
import Johnson.AtFull.Made.ScalarsLaw
import Johnson.Goal.Written.Made

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten.Joined (writtenSized)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem scalars_on_key :
    scalarsOn writtenSized.key.set (lookupsList writtenSized.key) = 34933 := by decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.scalars_on_key
