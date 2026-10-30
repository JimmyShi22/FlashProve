-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Link0Borders.lean: the six written values that the lines of the layers' link 0
name, gathered in one record (LayersBorders, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
A definition and nothing more.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.LayersLinkRuns
import ShapeLines.Borders.Border1
import ShapeLines.Borders.Border4LessLayersParts
import ShapeLines.Borders.Border5LessLayersParts
import ShapeLines.Borders.Border9LessLayersParts
import ShapeLines.Borders.Border10LessLayersParts
import ShapeLines.Borders.Border15

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The six written values of link 0. -/
def layersBorders0 : LayersBorders :=
  ⟨border1,
    border4LessLayersParts,
    border5LessLayersParts,
    border9LessLayersParts,
    border10LessLayersParts,
    border15⟩

end ShapeLines
