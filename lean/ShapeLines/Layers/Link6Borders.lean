-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Link6Borders.lean: the six written values that the lines of the layers' link 6
name, gathered in one record (LayersBorders, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
A definition and nothing more.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.LayersLinkRuns
import ShapeLines.Borders.Border85
import ShapeLines.Borders.Border88LessLayersParts
import ShapeLines.Borders.Border89LessLayersParts
import ShapeLines.Borders.Border93LessLayersParts
import ShapeLines.Borders.Border94LessLayersParts
import ShapeLines.Borders.Border99

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The six written values of link 6. -/
def layersBorders6 : LayersBorders :=
  ⟨border85,
    border88LessLayersParts,
    border89LessLayersParts,
    border93LessLayersParts,
    border94LessLayersParts,
    border99⟩

end ShapeLines
