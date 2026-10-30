-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Plan/FromLayout.lean: from the layout of a model's committed matrix to what the key's proof
of the ranges looks up.

The rule. Every unit of the layout counts, in the layout's order. A unit's number of digits is the
one that the layout gives it, 2 or 4; any other number is refused. All rows of the matrix are
ranged. So the rows between the end of the last unit and the end of the matrix, which a layout adds
to round the number of rows up, hold bytes only, in pairs of neighbours.

Main definitions: unitsOfLayout, layoutOk, shapeOfLayout.
C++ counterpart: wf_units_of_layout, wf_layout_fault and wf_shape_of_layout in
blocks/frame/wf_units.h.

Not claimed here: which units have four digits. A unit of four digits gets the statement on bytes
and no statement on its numbers. This file takes what the layout says: both sides form the layout
from the public files, and what follows from the shape is bound as the item "ranges" in the
parameter bytes of the key's first chain. A caller that wants four digits for certain units only
must test its own layout, as Model.Verify.shapesWith does for the model.
-/
import OnBytes.Plan.Units
import OnBytes.Model.Weights

namespace OnBytes.Plan

/-- The units of a layout. -/
def unitsOfLayout (Y : Model.WsLay) : List RowUnit :=
  Y.U.toList.map fun u => ⟨u.off, u.rows, u.nlw⟩

/-- True if the layout's units pass unitsOk, with all rows of the matrix ranged. -/
def layoutOk (Y : Model.WsLay) : Bool := unitsOk Y.m0 Y.m0 (unitsOfLayout Y)

/-- What the key's proof of the ranges looks up, for a layout and 2^kCol columns. Nothing if
layoutOk fails. -/
def shapeOfLayout (Y : Model.WsLay) (kCol : Nat) : Option Shape :=
  shapeOfUnits kCol Y.m0 Y.m0 (unitsOfLayout Y)

end OnBytes.Plan
