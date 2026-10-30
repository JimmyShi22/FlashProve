-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Link16Borders.lean: the six written values that the lines of the layers' link 16
name, gathered in one record (LayersBorders, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
A definition and nothing more.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.LayersLinkRuns
import ShapeLines.Borders.Border225
import ShapeLines.Borders.Border228LessLayersParts
import ShapeLines.Borders.Border229LessLayersParts
import ShapeLines.Borders.Border233LessLayersParts
import ShapeLines.Borders.Border234LessLayersParts
import ShapeLines.Borders.Border239

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The six written values of link 16. -/
def layersBorders16 : LayersBorders :=
  ⟨border225,
    border228LessLayersParts,
    border229LessLayersParts,
    border233LessLayersParts,
    border234LessLayersParts,
    border239⟩

end ShapeLines
