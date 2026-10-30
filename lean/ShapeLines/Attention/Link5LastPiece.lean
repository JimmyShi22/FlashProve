-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Attention/Link5LastPiece.lean: one closed line: attention link 5, members 80 to 84.
How. The statement equates a closed Bool with true. The proof term is Eq.refl true; kernel_rfl
leaves the comparison of the two sides to Lean's kernel.
Limits. Alone this line can be true although the batching, or the members before it, returned an
error: where the batching's run did, look and lookHeard in this line's start are none. Only with
this link's three other lines, four_all and the layout file's size does it say that the link runs
from border71. Nothing here says that the run from the first shape reaches border71. The steps are
those of TabLight.lean's cells, not those of shapeL (LWn X). The record is the one that atXLC
hands in (AtX.lean, AtXCounts.lean), not what publicOfO returns. four_all carries the line over,
by cellsH_eq and atXLC_zFull.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.JoinHalves
import Johnson.Unfolds.KernelRfl
import ShapeLines.ClosingHint
import ShapeLines.Borders.Border71
import ShapeLines.Borders.Border79LessPair
import ShapeLines.Borders.Border80LessPair
import ShapeLines.Borders.Border85

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.PairAside

-- The comparison is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- From border80LessPair with the look and lookHeard that the batching left, members 80 to 84
return border85, all components compared. (Premise P3 of four_all.) -/
theorem attentionLink5_lastPiece :
    atXLC (fun X =>
      wholeB
        (runH closingHint X (71 + 8 + 1) 5
          (withLk border80LessPair (lkB closingHint 71 8 1 border71 border79LessPair X)))
        border85) = true := by
  kernel_rfl

end ShapeLines

#print axioms ShapeLines.attentionLink5_lastPiece
