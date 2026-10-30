-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Plan4Lines.lean: the ten closed lines on the plan of group 4, gathered in one
record (PlanLines, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import ShapeLines.Layers.Plan4Covers
import ShapeLines.Layers.Plan4Numbers
import ShapeLines.Layers.Plan4Points
import ShapeLines.Layers.Plan4Small
import ShapeLines.Layers.Plan4Panels
import ShapeLines.Layers.Plan4ClaimsCount
import ShapeLines.Layers.Plan4ClaimsFirstHalf
import ShapeLines.Layers.Plan4ClaimsSecondHalf
import ShapeLines.Layers.Plan4ClaimEmbedding
import ShapeLines.Layers.Plan4Join

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The ten closed lines on the plan of group 4. -/
theorem layersPlan4_lines : PlanLines 4 where
  covers := layersPlan4_covers
  numbers := layersPlan4_numbers
  points := layersPlan4_points
  small := layersPlan4_small
  panels := layersPlan4_panels
  claimsCount := layersPlan4_claimsCount
  claimsFirstHalf := layersPlan4_claimsFirstHalf
  claimsSecondHalf := layersPlan4_claimsSecondHalf
  claimEmbedding := layersPlan4_claimEmbedding
  join := layersPlan4_join

end ShapeLines

#print axioms ShapeLines.layersPlan4_lines
