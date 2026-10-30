-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Plan8Lines.lean: the ten closed lines on the plan of group 8, gathered in one
record (PlanLines, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import ShapeLines.Layers.Plan8Covers
import ShapeLines.Layers.Plan8Numbers
import ShapeLines.Layers.Plan8Points
import ShapeLines.Layers.Plan8Small
import ShapeLines.Layers.Plan8Panels
import ShapeLines.Layers.Plan8ClaimsCount
import ShapeLines.Layers.Plan8ClaimsFirstHalf
import ShapeLines.Layers.Plan8ClaimsSecondHalf
import ShapeLines.Layers.Plan8ClaimEmbedding
import ShapeLines.Layers.Plan8Join

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The ten closed lines on the plan of group 8. -/
theorem layersPlan8_lines : PlanLines 8 where
  covers := layersPlan8_covers
  numbers := layersPlan8_numbers
  points := layersPlan8_points
  small := layersPlan8_small
  panels := layersPlan8_panels
  claimsCount := layersPlan8_claimsCount
  claimsFirstHalf := layersPlan8_claimsFirstHalf
  claimsSecondHalf := layersPlan8_claimsSecondHalf
  claimEmbedding := layersPlan8_claimEmbedding
  join := layersPlan8_join

end ShapeLines

#print axioms ShapeLines.layersPlan8_lines
