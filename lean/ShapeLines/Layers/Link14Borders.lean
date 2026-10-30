-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Link14Borders.lean: the six written values that the lines of the layers' link 14
name, gathered in one record (LayersBorders, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
A definition and nothing more.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.LayersLinkRuns
import ShapeLines.Borders.Border197
import ShapeLines.Borders.Border200LessLayersParts
import ShapeLines.Borders.Border201LessLayersParts
import ShapeLines.Borders.Border205LessLayersParts
import ShapeLines.Borders.Border206LessLayersParts
import ShapeLines.Borders.Border211

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The six written values of link 14. -/
def layersBorders14 : LayersBorders :=
  ⟨border197,
    border200LessLayersParts,
    border201LessLayersParts,
    border205LessLayersParts,
    border206LessLayersParts,
    border211⟩

end ShapeLines
