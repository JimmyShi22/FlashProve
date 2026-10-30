-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Plan2Lines.lean: the ten closed lines on the plan of group 2, gathered in one
record (PlanLines, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import ShapeLines.Layers.Plan2Covers
import ShapeLines.Layers.Plan2Numbers
import ShapeLines.Layers.Plan2Points
import ShapeLines.Layers.Plan2Small
import ShapeLines.Layers.Plan2Panels
import ShapeLines.Layers.Plan2ClaimsCount
import ShapeLines.Layers.Plan2ClaimsFirstHalf
import ShapeLines.Layers.Plan2ClaimsSecondHalf
import ShapeLines.Layers.Plan2ClaimEmbedding
import ShapeLines.Layers.Plan2Join

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The ten closed lines on the plan of group 2. -/
theorem layersPlan2_lines : PlanLines 2 where
  covers := layersPlan2_covers
  numbers := layersPlan2_numbers
  points := layersPlan2_points
  small := layersPlan2_small
  panels := layersPlan2_panels
  claimsCount := layersPlan2_claimsCount
  claimsFirstHalf := layersPlan2_claimsFirstHalf
  claimsSecondHalf := layersPlan2_claimsSecondHalf
  claimEmbedding := layersPlan2_claimEmbedding
  join := layersPlan2_join

end ShapeLines

#print axioms ShapeLines.layersPlan2_lines
