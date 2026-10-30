-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Link2Borders.lean: the six written values that the lines of the layers' link 2
name, gathered in one record (LayersBorders, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
A definition and nothing more.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.LayersLinkRuns
import ShapeLines.Borders.Border29
import ShapeLines.Borders.Border32LessLayersParts
import ShapeLines.Borders.Border33LessLayersParts
import ShapeLines.Borders.Border37LessLayersParts
import ShapeLines.Borders.Border38LessLayersParts
import ShapeLines.Borders.Border43

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The six written values of link 2. -/
def layersBorders2 : LayersBorders :=
  ⟨border29,
    border32LessLayersParts,
    border33LessLayersParts,
    border37LessLayersParts,
    border38LessLayersParts,
    border43⟩

end ShapeLines
