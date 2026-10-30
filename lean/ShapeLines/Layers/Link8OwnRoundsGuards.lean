-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Link8OwnRoundsGuards.lean: one closed line: the layers' link 8, member 116, the
layers' own rounds: its guards on the shape before it.
How. The statement equates a closed Bool with true. The proof term is Eq.refl true; kernel_rfl
leaves the comparison of the two sides to Lean's kernel.
Limits. Alone this line can be true although the run of members 113 to 115 returned an error: the
layers' parts in its start are then the empty ones. Only with this link's sixteen other lines,
layersLink_runs and the layout file's size does it say that the link runs from border113. Nothing
here says that the run from the first shape reaches border113. The test is not the member's step:
from this line, the two other lines on this member and the ten lines on the plan, ownRounds_given
(Johnson/AtFull/Shape/Lines/Layers/OwnRoundsByTests.lean) concludes that the step of shapeL (LWn X)
returns, and what it returns but for the layers' parts, at the layout yFull; that the record has
that layout, y_at_zFull (AtXCounts.lean) concludes from the layout file's size. The start holds a
run over TabLight.lean's cells, not over those of shapeL (LWn X). The record is the one that
atXLC hands in (AtX.lean, AtXCounts.lean), not what publicOfO returns. layersLink_runs
(Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean) carries the line over, by cellsH_eq, whose
premise hpad_of_public pays at what publicOfO returns (TabLight.lean), and atXLC_zFull.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.LayersLinkRuns
import Johnson.Unfolds.KernelRfl
import ShapeLines.ClosingHint
import ShapeLines.Layers.Link8Borders

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

-- The limit of heartbeats is lifted for the comparison.
set_option maxHeartbeats 0 in
/-- The record has a plan of group 4, and the three guards of member 116 that read the shape accept
border116LessLayersParts with the layers' parts that members 113 to 115 left. -/
theorem layersLink8_ownRoundsGuards :
    lineOwnRoundsGuards closingHint 8 layersBorders8 = true := by
  kernel_rfl

end ShapeLines

#print axioms ShapeLines.layersLink8_ownRoundsGuards
