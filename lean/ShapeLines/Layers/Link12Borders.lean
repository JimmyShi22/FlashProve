-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Layers/Link12Borders.lean: the six written values that the lines of the layers' link 12
name, gathered in one record (LayersBorders, Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean).
A definition and nothing more.
Words, cost and the limits common to this library: ShapeLines/README.md. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.LayersLinkRuns
import ShapeLines.Borders.Border169
import ShapeLines.Borders.Border172LessLayersParts
import ShapeLines.Borders.Border173LessLayersParts
import ShapeLines.Borders.Border177LessLayersParts
import ShapeLines.Borders.Border178LessLayersParts
import ShapeLines.Borders.Border183

set_option autoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Layers

/-- The six written values of link 12. -/
def layersBorders12 : LayersBorders :=
  ⟨border169,
    border172LessLayersParts,
    border173LessLayersParts,
    border177LessLayersParts,
    border178LessLayersParts,
    border183⟩

end ShapeLines
