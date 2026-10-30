-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Plan10Lines.lean: the ten closed lines on the plan of group 10, gathered in one
record (PlanLines, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import ShapeLines.Layers.Plan10Covers
import ShapeLines.Layers.Plan10Numbers
import ShapeLines.Layers.Plan10Points
import ShapeLines.Layers.Plan10Small
import ShapeLines.Layers.Plan10Panels
import ShapeLines.Layers.Plan10ClaimsCount
import ShapeLines.Layers.Plan10ClaimsFirstHalf
import ShapeLines.Layers.Plan10ClaimsSecondHalf
import ShapeLines.Layers.Plan10ClaimEmbedding
import ShapeLines.Layers.Plan10Join

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The ten closed lines on the plan of group 10. -/
theorem layersPlan10_lines : PlanLines 10 where
  covers := layersPlan10_covers
  numbers := layersPlan10_numbers
  points := layersPlan10_points
  small := layersPlan10_small
  panels := layersPlan10_panels
  claimsCount := layersPlan10_claimsCount
  claimsFirstHalf := layersPlan10_claimsFirstHalf
  claimsSecondHalf := layersPlan10_claimsSecondHalf
  claimEmbedding := layersPlan10_claimEmbedding
  join := layersPlan10_join

end ShapeLines

#print axioms ShapeLines.layersPlan10_lines
