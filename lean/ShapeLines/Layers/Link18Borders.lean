-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Link18Borders.lean: the six written values that the lines of the layers' link 18
name, gathered in one record (LayersBorders, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
A definition and nothing more.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.LayersLinkRuns
import ShapeLines.Borders.Border253
import ShapeLines.Borders.Border256LessLayersParts
import ShapeLines.Borders.Border257LessLayersParts
import ShapeLines.Borders.Border261LessLayersParts
import ShapeLines.Borders.Border262LessLayersParts
import ShapeLines.Borders.Border267

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The six written values of link 18. -/
def layersBorders18 : LayersBorders :=
  ⟨border253,
    border256LessLayersParts,
    border257LessLayersParts,
    border261LessLayersParts,
    border262LessLayersParts,
    border267⟩

end ShapeLines
