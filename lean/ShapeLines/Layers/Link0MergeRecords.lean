-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Link0MergeRecords.lean: one closed line: the layers' link 0, member 4: what is
left of each weight claim.
How. The statement equates a closed Bool with true. atXLC_of_light
(Johnson/AtFull/Shape/Lines/Layers/PublicRecordLight.lean) draws it from the same test under
atXLLight, a second text of atXL. For that equation the proof term is Eq.refl true; kernel_rfl
leaves the comparison of the two sides to Lean's kernel.
Limits. It reads no run and no start, only the record and one list inside border5LessLayersParts.
Only with this link's sixteen other lines, layersLink_runs and the layout file's size does it say
that the link runs from border1. The test is not the member's step: from this line, the two other
lines on this member and the ten lines on the plan, ownRounds_given
(Johnson/AtFull/Shape/Lines/Layers/OwnRoundsByTests.lean) concludes that the step of shapeL (LWn X)
returns, and what it returns but for the layers' parts, at the layout yFull; that the record has
that layout, y_at_zFull (AtXCounts.lean) concludes from the layout file's size. The record is the
one that atXLC hands in (AtX.lean, AtXCounts.lean), not what publicOfO returns. layersLink_runs
(Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean) carries the line over, by atXLC_zFull.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.LayersLinkRuns
import Johnson.Unfolds.KernelRfl
import Johnson.AtFull.Shape.Lines.Layers.PublicRecordLight
import ShapeLines.Layers.Link0Borders

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

-- The limit of heartbeats is lifted for the comparison.
set_option maxHeartbeats 0 in
/-- The record has a plan of group 0, and the list of what is left of each weight claim, made from
the plan, agrees with the list that border5LessLayersParts holds. -/
theorem layersLink0_mergeRecords :
    lineMergeRecords 0 layersBorders0 = true :=
  atXLC_of_light (by kernel_rfl)

end ShapeLines

#print axioms ShapeLines.layersLink0_mergeRecords
