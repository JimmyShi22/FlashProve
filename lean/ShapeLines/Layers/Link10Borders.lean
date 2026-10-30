-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Link10Borders.lean: the six written values that the lines of the layers' link 10
name, gathered in one record (LayersBorders, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
A definition and nothing more.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.LayersLinkRuns
import ShapeLines.Borders.Border141
import ShapeLines.Borders.Border144LessLayersParts
import ShapeLines.Borders.Border145LessLayersParts
import ShapeLines.Borders.Border149LessLayersParts
import ShapeLines.Borders.Border150LessLayersParts
import ShapeLines.Borders.Border155

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The six written values of link 10. -/
def layersBorders10 : LayersBorders :=
  ⟨border141,
    border144LessLayersParts,
    border145LessLayersParts,
    border149LessLayersParts,
    border150LessLayersParts,
    border155⟩

end ShapeLines
