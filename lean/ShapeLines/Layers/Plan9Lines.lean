-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Plan9Lines.lean: the ten closed lines on the plan of group 9, gathered in one
record (PlanLines, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import ShapeLines.Layers.Plan9Covers
import ShapeLines.Layers.Plan9Numbers
import ShapeLines.Layers.Plan9Points
import ShapeLines.Layers.Plan9Small
import ShapeLines.Layers.Plan9Panels
import ShapeLines.Layers.Plan9ClaimsCount
import ShapeLines.Layers.Plan9ClaimsFirstHalf
import ShapeLines.Layers.Plan9ClaimsSecondHalf
import ShapeLines.Layers.Plan9ClaimEmbedding
import ShapeLines.Layers.Plan9Join

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The ten closed lines on the plan of group 9. -/
theorem layersPlan9_lines : PlanLines 9 where
  covers := layersPlan9_covers
  numbers := layersPlan9_numbers
  points := layersPlan9_points
  small := layersPlan9_small
  panels := layersPlan9_panels
  claimsCount := layersPlan9_claimsCount
  claimsFirstHalf := layersPlan9_claimsFirstHalf
  claimsSecondHalf := layersPlan9_claimsSecondHalf
  claimEmbedding := layersPlan9_claimEmbedding
  join := layersPlan9_join

end ShapeLines

#print axioms ShapeLines.layersPlan9_lines
