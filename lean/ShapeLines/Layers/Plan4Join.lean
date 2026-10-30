-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Plan4Join.lean: one closed line: at the plan of group 4, the join's test accepts.
How. The statement equates a closed Bool with true. atXLC_of_light
(Johnson/AtFull/Shape/Lines/Layers/PublicRecordLight.lean) draws it from the same test under
atXLLight, a second text of atXL. For that equation the proof term is Eq.refl true; kernel_rfl
leaves the comparison of the two sides to Lean's kernel.
Limits. Alone it says nothing of the run. The test reads the record alone and no shape; it is one of
ten that together give the test on the plan inside the step of the layers' own rounds
(planTest_of_tests, Johnson/AtFull/Shape/Lines/Layers/OwnRoundsByTests.lean). The record is the one
that atXLC hands in (AtX.lean, AtXCounts.lean), not what publicOfO returns. layersLink_runs
(Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean) carries the line over, by atXLC_zFull.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.LayersLinkRuns
import Johnson.AtFull.Shape.Lines.Layers.PublicRecordLight
import Johnson.Unfolds.KernelRfl

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

-- The limit of heartbeats is lifted for the comparison.
set_option maxHeartbeats 0 in
/-- The record has a plan of group 4, and the join's test accepts. -/
theorem layersPlan4_join :
    atXLC (planJoin 4) = true :=
  atXLC_of_light (by kernel_rfl)

end ShapeLines

#print axioms ShapeLines.layersPlan4_join
