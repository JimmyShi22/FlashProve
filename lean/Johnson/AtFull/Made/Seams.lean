-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/Seams.lean: THREE SMALL SEAMS BETWEEN WRITTEN VALUES OF DIFFERENT HANDS, for the
join of the ledger of the planner's second half (Johnson/AtFull/Made/Ledger.lean). Closed facts by
Lean's kernel, each with a bent twin that fails, and one law.

  **`moments_seam`** : declaredFull.map (·.moment) = declaredW.map (·.moment): what the 25 segments
    declare, as LinksFull.lean makes it by a rule (at which `links_return` ends the premise a₄), has
    the moments of the literal of DeclaredLit.lean (which `reqFrame_of_pub` asks for the premise
    b₂). `moments_seam_rows`: with one declared array's rows one higher (LinksFull.lean's
    declaredBent): no. `moments_seam_pop`: without the last segment: no.
  **`declared_size`** : declaredFull.size = 25 (`shapes_and_sizes`' hd). `declared_size_pop`.
  **`matrixRows_written`** : proofSizedFull.batch.shape.matrixRows = 3076096, and `p4_of_first`: so
    FirstWritten f gives f.lin.matrixRows = 3076096 (`built_at_full`'s p₄). `matrixRows_no`.
Limits. Equations between written values: that a routine returns one of them at any public files is
not said. Nothing on soundness.

-/
import Johnson.AtFull.Made.LinksFull
import Johnson.AtFull.Made.DeclaredLit
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made

open VerifiableInference.PlanWritten (proofSizedFull FirstWritten)

/-- **The two written declarations have the same moments.** -/
theorem moments_seam : declaredFull.map (·.moment) = declaredW.map (·.moment) := by decide +kernel

/-- A bent twin: one declared array's rows one higher. -/
theorem moments_seam_rows :
    decide (declaredBent.map (·.moment) = declaredW.map (·.moment)) = false := by decide +kernel

/-- A bent twin: without the last segment. -/
theorem moments_seam_pop :
    decide (declaredFull.pop.map (·.moment) = declaredW.map (·.moment)) = false := by
  decide +kernel

/-- **25 segments declare.** -/
theorem declared_size : declaredFull.size = 25 := by decide +kernel

/-- A bent twin. -/
theorem declared_size_pop : decide (declaredFull.pop.size = 25) = false := by decide +kernel

/-- **The rows of the committed table's matrix in the written shape of the test on the table.** -/
theorem matrixRows_written : proofSizedFull.batch.shape.matrixRows = 3076096 := by decide +kernel

/-- A bent twin. -/
theorem matrixRows_no : decide (proofSizedFull.batch.shape.matrixRows = 3076097) = false := by
  decide +kernel

/-- So of a first chain's parameters that are the written ones. -/
theorem p4_of_first {f : OnBytes.Params.First} (h : FirstWritten f) :
    f.lin.matrixRows = 3076096 := by
  rw [h.2.1]
  exact matrixRows_written

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.moments_seam
#print axioms Johnson.AtFull.Made.moments_seam_rows
#print axioms Johnson.AtFull.Made.moments_seam_pop
#print axioms Johnson.AtFull.Made.declared_size
#print axioms Johnson.AtFull.Made.declared_size_pop
#print axioms Johnson.AtFull.Made.matrixRows_written
#print axioms Johnson.AtFull.Made.matrixRows_no
#print axioms Johnson.AtFull.Made.p4_of_first
