-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Plan7Lines.lean: the ten closed lines on the plan of group 7, gathered in one
record (PlanLines, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import ShapeLines.Layers.Plan7Covers
import ShapeLines.Layers.Plan7Numbers
import ShapeLines.Layers.Plan7Points
import ShapeLines.Layers.Plan7Small
import ShapeLines.Layers.Plan7Panels
import ShapeLines.Layers.Plan7ClaimsCount
import ShapeLines.Layers.Plan7ClaimsFirstHalf
import ShapeLines.Layers.Plan7ClaimsSecondHalf
import ShapeLines.Layers.Plan7ClaimEmbedding
import ShapeLines.Layers.Plan7Join

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The ten closed lines on the plan of group 7. -/
theorem layersPlan7_lines : PlanLines 7 where
  covers := layersPlan7_covers
  numbers := layersPlan7_numbers
  points := layersPlan7_points
  small := layersPlan7_small
  panels := layersPlan7_panels
  claimsCount := layersPlan7_claimsCount
  claimsFirstHalf := layersPlan7_claimsFirstHalf
  claimsSecondHalf := layersPlan7_claimsSecondHalf
  claimEmbedding := layersPlan7_claimEmbedding
  join := layersPlan7_join

end ShapeLines

#print axioms ShapeLines.layersPlan7_lines
