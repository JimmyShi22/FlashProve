-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Cut/CutRefuses.lean: A NEGATIVE TEST TO `cut_written`
(Johnson/AtFull/Cut/CutAtWritten.lean): with ONE entry struck from the written rounds' entries, the
LAST ("SEAL"), the table is refused: `cutOf … = none`: the grammar walks all 25 links, the finish
and the members' places before it can say so. One decision of Lean's kernel, at the eager twin.
Limits. One fault at one place. The full size alone. Nothing on soundness. On hiding nothing.

-/
import Johnson.G.DryProofLit
import Johnson.AtFull.Cut.CutEager

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Cut
open VerifiableInference.Desc.First
open Johnson.G (dryProofFull)

set_option maxRecDepth 1000000 in
theorem cutK_refuses : (cutOfK (dryProofFull.1.map (·.1.entry)).dropLast).isNone = true := by
  decide +kernel

/-- **With the last entry struck the table is refused.** -/
theorem cut_refuses : (cutOf (dryProofFull.1.map (·.1.entry)).dropLast).isNone = true := by
  rw [← cutOfK_eq]
  exact cutK_refuses

end Johnson.AtFull.Cut

#print axioms Johnson.AtFull.Cut.cutK_refuses
#print axioms Johnson.AtFull.Cut.cut_refuses
