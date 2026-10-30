-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Plan0Lines.lean: the ten closed lines on the plan of group 0, gathered in one
record (PlanLines, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import ShapeLines.Layers.Plan0Covers
import ShapeLines.Layers.Plan0Numbers
import ShapeLines.Layers.Plan0Points
import ShapeLines.Layers.Plan0Small
import ShapeLines.Layers.Plan0Panels
import ShapeLines.Layers.Plan0ClaimsCount
import ShapeLines.Layers.Plan0ClaimsFirstHalf
import ShapeLines.Layers.Plan0ClaimsSecondHalf
import ShapeLines.Layers.Plan0ClaimEmbedding
import ShapeLines.Layers.Plan0Join

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The ten closed lines on the plan of group 0. -/
theorem layersPlan0_lines : PlanLines 0 where
  covers := layersPlan0_covers
  numbers := layersPlan0_numbers
  points := layersPlan0_points
  small := layersPlan0_small
  panels := layersPlan0_panels
  claimsCount := layersPlan0_claimsCount
  claimsFirstHalf := layersPlan0_claimsFirstHalf
  claimsSecondHalf := layersPlan0_claimsSecondHalf
  claimEmbedding := layersPlan0_claimEmbedding
  join := layersPlan0_join

end ShapeLines

#print axioms ShapeLines.layersPlan0_lines
