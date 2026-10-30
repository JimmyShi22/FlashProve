-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Attention/Link21LastPiece.lean: one closed line: attention link 21, members 304 to 308.
How. The statement equates a closed Bool with true. The proof term is Eq.refl true; kernel_rfl
leaves the comparison of the two sides to Lean's kernel.
Limits. Alone this line can be true although the batching, or the members before it, returned an
error: where the batching's run did, look and lookHeard in this line's start are none. Only with
this link's three other lines, four_all and the layout file's size does it say that the link runs
from border295. Nothing here says that the run from the first shape reaches border295. The steps are
those of TabLight.lean's cells, not those of shapeL (LWn X). The record is the one that atXLC
hands in (AtX.lean, AtXCounts.lean), not what publicOfO returns. four_all carries the line over,
by cellsH_eq and atXLC_zFull.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.JoinHalves
import Johnson.Unfolds.KernelRfl
import ShapeLines.ClosingHint
import ShapeLines.Borders.Border295
import ShapeLines.Borders.Border303LessPair
import ShapeLines.Borders.Border304LessPair
import ShapeLines.Borders.Border309

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.PairAside

-- The comparison is long: the limit of heartbeats is lifted.
set_option maxHeartbeats 0 in
/-- From border304LessPair with the look and lookHeard that the batching left, members 304 to 308
return border309, all components compared. (Premise P3 of four_all.) -/
theorem attentionLink21_lastPiece :
    atXLC (fun X =>
      wholeB
        (runH closingHint X (295 + 8 + 1) 5
          (withLk border304LessPair (lkB closingHint 295 8 1 border295 border303LessPair X)))
        border309) = true := by
  kernel_rfl

end ShapeLines

#print axioms ShapeLines.attentionLink21_lastPiece
