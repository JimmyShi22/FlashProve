-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Link4Borders.lean: the six written values that the lines of the layers' link 4
name, gathered in one record (LayersBorders, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
A definition and nothing more.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.LayersLinkRuns
import ShapeLines.Borders.Border57
import ShapeLines.Borders.Border60LessLayersParts
import ShapeLines.Borders.Border61LessLayersParts
import ShapeLines.Borders.Border65LessLayersParts
import ShapeLines.Borders.Border66LessLayersParts
import ShapeLines.Borders.Border71

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The six written values of link 4. -/
def layersBorders4 : LayersBorders :=
  ⟨border57,
    border60LessLayersParts,
    border61LessLayersParts,
    border65LessLayersParts,
    border66LessLayersParts,
    border71⟩

end ShapeLines
