-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Plan5Lines.lean: the ten closed lines on the plan of group 5, gathered in one
record (PlanLines, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import ShapeLines.Layers.Plan5Covers
import ShapeLines.Layers.Plan5Numbers
import ShapeLines.Layers.Plan5Points
import ShapeLines.Layers.Plan5Small
import ShapeLines.Layers.Plan5Panels
import ShapeLines.Layers.Plan5ClaimsCount
import ShapeLines.Layers.Plan5ClaimsFirstHalf
import ShapeLines.Layers.Plan5ClaimsSecondHalf
import ShapeLines.Layers.Plan5ClaimEmbedding
import ShapeLines.Layers.Plan5Join

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The ten closed lines on the plan of group 5. -/
theorem layersPlan5_lines : PlanLines 5 where
  covers := layersPlan5_covers
  numbers := layersPlan5_numbers
  points := layersPlan5_points
  small := layersPlan5_small
  panels := layersPlan5_panels
  claimsCount := layersPlan5_claimsCount
  claimsFirstHalf := layersPlan5_claimsFirstHalf
  claimsSecondHalf := layersPlan5_claimsSecondHalf
  claimEmbedding := layersPlan5_claimEmbedding
  join := layersPlan5_join

end ShapeLines

#print axioms ShapeLines.layersPlan5_lines
