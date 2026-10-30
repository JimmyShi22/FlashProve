-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Link8Borders.lean: the six written values that the lines of the layers' link 8
name, gathered in one record (LayersBorders, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
A definition and nothing more.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.LayersLinkRuns
import ShapeLines.Borders.Border113
import ShapeLines.Borders.Border116LessLayersParts
import ShapeLines.Borders.Border117LessLayersParts
import ShapeLines.Borders.Border121LessLayersParts
import ShapeLines.Borders.Border122LessLayersParts
import ShapeLines.Borders.Border127

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The six written values of link 8. -/
def layersBorders8 : LayersBorders :=
  ⟨border113,
    border116LessLayersParts,
    border117LessLayersParts,
    border121LessLayersParts,
    border122LessLayersParts,
    border127⟩

end ShapeLines
