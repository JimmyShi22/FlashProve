-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Attention/Link23LastPiece.lean: one closed line: attention link 23, members 332 to 336.
How. The statement equates a closed Bool with true. The proof term is Eq.refl true; kernel_rfl
leaves the comparison of the two sides to Lean's kernel.
Limits. Alone this line can be true although the batching, or the members before it, returned an
error: where the batching's run did, look and lookHeard in this line's start are none. Only with
this link's three other lines, four_all and the layout file's size does it say that the link runs
from border323. Nothing here says that the run from the first shape reaches border323. The steps are
those of TabLight.lean's cells, not those of shapeL (LWn X). The record is the one that atXLC
hands in (AtX.lean, AtXCounts.lean), not what publicOfO returns. four_all carries the line over,
by cellsH_eq and atXLC_zFull.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.JoinHalves
import Johnson.Unfolds.KernelRfl
import ShapeLines.ClosingHint
import ShapeLines.Borders.Border323
import ShapeLines.Borders.Border331LessPair
import ShapeLines.Borders.Border332LessPair
import ShapeLines.Borders.Border337

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.PairAside

-- The comparison is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- From border332LessPair with the look and lookHeard that the batching left, members 332 to 336
return border337, all components compared. (Premise P3 of four_all.) -/
theorem attentionLink23_lastPiece :
    atXLC (fun X =>
      wholeB
        (runH closingHint X (323 + 8 + 1) 5
          (withLk border332LessPair (lkB closingHint 323 8 1 border323 border331LessPair X)))
        border337) = true := by
  kernel_rfl

end ShapeLines

#print axioms ShapeLines.attentionLink23_lastPiece
