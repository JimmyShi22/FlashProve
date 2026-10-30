-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Link20Borders.lean: the six written values that the lines of the layers' link 20
name, gathered in one record (LayersBorders, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
A definition and nothing more.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.LayersLinkRuns
import ShapeLines.Borders.Border281
import ShapeLines.Borders.Border284LessLayersParts
import ShapeLines.Borders.Border285LessLayersParts
import ShapeLines.Borders.Border289LessLayersParts
import ShapeLines.Borders.Border290LessLayersParts
import ShapeLines.Borders.Border295

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The six written values of link 20. -/
def layersBorders20 : LayersBorders :=
  ⟨border281,
    border284LessLayersParts,
    border285LessLayersParts,
    border289LessLayersParts,
    border290LessLayersParts,
    border295⟩

end ShapeLines
