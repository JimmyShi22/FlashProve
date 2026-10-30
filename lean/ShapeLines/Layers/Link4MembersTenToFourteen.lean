-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Link4MembersTenToFourteen.lean: one closed line: the layers' link 4, members 66 to
70.
How. The statement equates a closed Bool with true. The proof term is Eq.refl true; kernel_rfl
leaves the comparison of the two sides to Lean's kernel.
Limits. Alone this line can be true although the run of member 65 returned an error: the layers'
parts in its start are then the empty ones. The parts in its start are a term that holds the run of
the table's own cell at member 65, which is the table's own batching and not the light step, in that
run's start the run of members 61 to 64, and in that one's start the run of the table's own cell at
member 60, with the hearing in it, and in its start the run of members 57 to 59; a line that opens a
part must bring these runs to their return. Whether this line opens one is not said. Only with this
link's sixteen other lines, layersLink_runs and the layout file's size does it say that the link
runs from border57. Nothing here says that the run from the first shape reaches border57. The steps
are those of TabLight.lean's cells, not those of shapeL (LWn X). The record is the one that
atXLC hands in (AtX.lean, AtXCounts.lean), not what publicOfO returns. layersLink_runs
(Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean) carries the line over, by cellsH_eq, whose
premise hpad_of_public pays at what publicOfO returns (TabLight.lean), and atXLC_zFull.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.LayersLinkRuns
import Johnson.Unfolds.KernelRfl
import ShapeLines.ClosingHint
import ShapeLines.Layers.Link4Borders

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

-- The limit of heartbeats is lifted for the comparison.
set_option maxHeartbeats 0 in
/-- From border66LessLayersParts with the layers' parts that member 65 left, members 66 to 70 return
border71, all components compared. -/
theorem layersLink4_membersTenToFourteen :
    lineMembersTenToFourteen closingHint 4 layersBorders4 = true := by
  kernel_rfl

end ShapeLines

#print axioms ShapeLines.layersLink4_membersTenToFourteen
