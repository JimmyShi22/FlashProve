-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Plan3Lines.lean: the ten closed lines on the plan of group 3, gathered in one
record (PlanLines, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import ShapeLines.Layers.Plan3Covers
import ShapeLines.Layers.Plan3Numbers
import ShapeLines.Layers.Plan3Points
import ShapeLines.Layers.Plan3Small
import ShapeLines.Layers.Plan3Panels
import ShapeLines.Layers.Plan3ClaimsCount
import ShapeLines.Layers.Plan3ClaimsFirstHalf
import ShapeLines.Layers.Plan3ClaimsSecondHalf
import ShapeLines.Layers.Plan3ClaimEmbedding
import ShapeLines.Layers.Plan3Join

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The ten closed lines on the plan of group 3. -/
theorem layersPlan3_lines : PlanLines 3 where
  covers := layersPlan3_covers
  numbers := layersPlan3_numbers
  points := layersPlan3_points
  small := layersPlan3_small
  panels := layersPlan3_panels
  claimsCount := layersPlan3_claimsCount
  claimsFirstHalf := layersPlan3_claimsFirstHalf
  claimsSecondHalf := layersPlan3_claimsSecondHalf
  claimEmbedding := layersPlan3_claimEmbedding
  join := layersPlan3_join

end ShapeLines

#print axioms ShapeLines.layersPlan3_lines
