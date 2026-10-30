-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Plan6Lines.lean: the ten closed lines on the plan of group 6, gathered in one
record (PlanLines, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import ShapeLines.Layers.Plan6Covers
import ShapeLines.Layers.Plan6Numbers
import ShapeLines.Layers.Plan6Points
import ShapeLines.Layers.Plan6Small
import ShapeLines.Layers.Plan6Panels
import ShapeLines.Layers.Plan6ClaimsCount
import ShapeLines.Layers.Plan6ClaimsFirstHalf
import ShapeLines.Layers.Plan6ClaimsSecondHalf
import ShapeLines.Layers.Plan6ClaimEmbedding
import ShapeLines.Layers.Plan6Join

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The ten closed lines on the plan of group 6. -/
theorem layersPlan6_lines : PlanLines 6 where
  covers := layersPlan6_covers
  numbers := layersPlan6_numbers
  points := layersPlan6_points
  small := layersPlan6_small
  panels := layersPlan6_panels
  claimsCount := layersPlan6_claimsCount
  claimsFirstHalf := layersPlan6_claimsFirstHalf
  claimsSecondHalf := layersPlan6_claimsSecondHalf
  claimEmbedding := layersPlan6_claimEmbedding
  join := layersPlan6_join

end ShapeLines

#print axioms ShapeLines.layersPlan6_lines
