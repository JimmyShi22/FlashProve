-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Plan11Lines.lean: the ten closed lines on the plan of group 11, gathered in one
record (PlanLines, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import ShapeLines.Layers.Plan11Covers
import ShapeLines.Layers.Plan11Numbers
import ShapeLines.Layers.Plan11Points
import ShapeLines.Layers.Plan11Small
import ShapeLines.Layers.Plan11Panels
import ShapeLines.Layers.Plan11ClaimsCount
import ShapeLines.Layers.Plan11ClaimsFirstHalf
import ShapeLines.Layers.Plan11ClaimsSecondHalf
import ShapeLines.Layers.Plan11ClaimEmbedding
import ShapeLines.Layers.Plan11Join

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The ten closed lines on the plan of group 11. -/
theorem layersPlan11_lines : PlanLines 11 where
  covers := layersPlan11_covers
  numbers := layersPlan11_numbers
  points := layersPlan11_points
  small := layersPlan11_small
  panels := layersPlan11_panels
  claimsCount := layersPlan11_claimsCount
  claimsFirstHalf := layersPlan11_claimsFirstHalf
  claimsSecondHalf := layersPlan11_claimsSecondHalf
  claimEmbedding := layersPlan11_claimEmbedding
  join := layersPlan11_join

end ShapeLines

#print axioms ShapeLines.layersPlan11_lines
