-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Attention/Link3FirstPiece.lean: one closed line: attention link 3, members 43 to 50.
How. The statement equates a closed Bool with true. The proof term is Eq.refl true; kernel_rfl
leaves the comparison of the two sides to Lean's kernel.
Limits. Nothing here says that the run from the first shape reaches border43. The steps are those of
TabLight.lean's cells, not those of shapeL (LWn X). The record is the one that atXLC hands in
(AtX.lean, AtXCounts.lean), not what publicOfO returns. four_all carries the line over, by
cellsH_eq and atXLC_zFull.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.JoinHalves
import Johnson.Unfolds.KernelRfl
import ShapeLines.ClosingHint
import ShapeLines.Borders.Border43
import ShapeLines.Borders.Border51LessPair

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.PairAside

-- The comparison is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- From border43, members 43 to 50 return a shape which, with look and lookHeard set to none, is
border51LessPair. (Premise P1 of four_all.) -/
theorem attentionLink3_firstPiece :
    atXLC (fun X => lessB (runH closingHint X 43 8 border43) border51LessPair) = true := by
  kernel_rfl

end ShapeLines

#print axioms ShapeLines.attentionLink3_firstPiece
