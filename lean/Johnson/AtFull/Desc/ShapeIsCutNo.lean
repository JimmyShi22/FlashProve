-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/ShapeIsCutNo.lean: the test of ShapeIsCut.lean (`shape_is`) can fail inside the
list too. The written shape keeps its 358 rows, and row 200 bears another name
(`shape_name_bent`), or a place one piece further (`shape_place_bent`): the test says no. (Were
there no row 200, the bent list would be the written one and the test would say yes.)
Closed statements
by evaluations in Lean's kernel, stated positively. No other file imports this one.

Limits. Written values, bent by hand. No soundness is claimed.
-/
import Johnson.AtFull.Desc.ShapeIsCut

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Desc
open VerifiableInference.Desc (Place)

/-- The written shape with row 200 turned by f. -/
def shapeBentBy (f : String × Place → String × Place) : List (String × Place) :=
  shapeW.zipIdx.map fun r => if r.2 == 200 then f r.1 else r.1

set_option maxHeartbeats 0 in
theorem shape_name_bent :
    decide (shapeMade = some (shapeBentBy fun r => ("bent", r.2))) = false := by decide +kernel

set_option maxHeartbeats 0 in
theorem shape_place_bent :
    decide (shapeMade = some (shapeBentBy fun r => (r.1, { r.2 with piece := r.2.piece + 1 }))) =
      false := by decide +kernel

end Johnson.AtFull.Desc

#print axioms Johnson.AtFull.Desc.shape_name_bent
#print axioms Johnson.AtFull.Desc.shape_place_bent
