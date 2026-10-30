-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Link22Borders.lean: the six written values that the lines of the layers' link 22
name, gathered in one record (LayersBorders, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
A definition and nothing more.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.LayersLinkRuns
import ShapeLines.Borders.Border309
import ShapeLines.Borders.Border312LessLayersParts
import ShapeLines.Borders.Border313LessLayersParts
import ShapeLines.Borders.Border317LessLayersParts
import ShapeLines.Borders.Border318LessLayersParts
import ShapeLines.Borders.Border323

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The six written values of link 22. -/
def layersBorders22 : LayersBorders :=
  ⟨border309,
    border312LessLayersParts,
    border313LessLayersParts,
    border317LessLayersParts,
    border318LessLayersParts,
    border323⟩

end ShapeLines
