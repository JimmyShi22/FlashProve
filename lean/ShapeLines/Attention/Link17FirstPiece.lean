-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Attention/Link17FirstPiece.lean: one closed line: attention link 17, members 239 to 246.
How. The statement equates a closed Bool with true. The proof term is Eq.refl true; kernel_rfl
leaves the comparison of the two sides to Lean's kernel.
Limits. Nothing here says that the run from the first shape reaches border239. The steps are those
of TabLight.lean's cells, not those of shapeL (LWn X). The record is the one that atXLC hands in
(AtX.lean, AtXCounts.lean), not what publicOfO returns. four_all carries the line over, by
cellsH_eq and atXLC_zFull.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.JoinHalves
import Johnson.Unfolds.KernelRfl
import ShapeLines.ClosingHint
import ShapeLines.Borders.Border239
import ShapeLines.Borders.Border247LessPair

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.PairAside

-- The comparison is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- From border239, members 239 to 246 return a shape which, with look and lookHeard set to none, is
border247LessPair. (Premise P1 of four_all.) -/
theorem attentionLink17_firstPiece :
    atXLC (fun X => lessB (runH closingHint X 239 8 border239) border247LessPair) = true := by
  kernel_rfl

end ShapeLines

#print axioms ShapeLines.attentionLink17_firstPiece
