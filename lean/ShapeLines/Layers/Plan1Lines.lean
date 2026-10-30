-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Plan1Lines.lean: the ten closed lines on the plan of group 1, gathered in one
record (PlanLines, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import ShapeLines.Layers.Plan1Covers
import ShapeLines.Layers.Plan1Numbers
import ShapeLines.Layers.Plan1Points
import ShapeLines.Layers.Plan1Small
import ShapeLines.Layers.Plan1Panels
import ShapeLines.Layers.Plan1ClaimsCount
import ShapeLines.Layers.Plan1ClaimsFirstHalf
import ShapeLines.Layers.Plan1ClaimsSecondHalf
import ShapeLines.Layers.Plan1ClaimEmbedding
import ShapeLines.Layers.Plan1Join

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The ten closed lines on the plan of group 1. -/
theorem layersPlan1_lines : PlanLines 1 where
  covers := layersPlan1_covers
  numbers := layersPlan1_numbers
  points := layersPlan1_points
  small := layersPlan1_small
  panels := layersPlan1_panels
  claimsCount := layersPlan1_claimsCount
  claimsFirstHalf := layersPlan1_claimsFirstHalf
  claimsSecondHalf := layersPlan1_claimsSecondHalf
  claimEmbedding := layersPlan1_claimEmbedding
  join := layersPlan1_join

end ShapeLines

#print axioms ShapeLines.layersPlan1_lines
