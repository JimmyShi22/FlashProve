-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ClearLight.lean: THE STEP "CLEARED" ON SHAPES (`clearG`, with `clearLayG` and
`clearHeadG`; Johnson/Desc/First/Walk/Shape/ClearRow.lean) ONCE MORE, OVER THE LIGHT PENDING ROW
(`pendSL`, PendShapeLight.lean): `clearGL`, `clearLayGL`, `clearHeadGL`; AND THE TEXTS ARE EQUAL AT
ALL ARGUMENTS. Three definitions, three general theorems; nothing is evaluated.

Purpose. At a layers' link and at the head's link the step lays the sub-proof's pending row: it
calls pendS, which builds vectors and arrays only to measure them (PendShapeLight.lean says which).
Whoever evaluates the step at the full size may evaluate the light text in its place.

Main names.
* `clearGL`, **`clearG_eq`**: clearG X lay lin countsB leftSh = clearGL X lay lin countsB leftSh.
  `clearLayGL`, **`clearLayG_eq`**. `clearHeadGL`, **`clearHeadG_eq`**.

Limits. EQUALITIES OF TWO TEXTS. Nothing says that a step returns. That the light text is cheap to
evaluate is not shown here. A SECOND TEXT: clearGL repeats clearG's text arm for arm; a change of
that text that breaks the equation stops the build. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Walk.Shape.ClearRow
import Johnson.AtFull.Shape.PendShapeLight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc.First.Shape
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Shape

/-- clearG's text (Johnson/Desc/First/Walk/Shape/ClearRow.lean) over the light pending row. -/
def clearGL (X : LinkPub) (lay : WsLay) (lin : LinShape) (countsB : ChainSh → Bool)
    (leftSh : ChainSh → Option MergeSh) (a : ChainSh) : Except String ChainSh :=
  match a.link, a.led with
  | some C, some L =>
    if clearB X countsB a C L then
      if X.fv then
        match leftSh a with
        | none => .error "W5: nothing is left for the row"
        | some w =>
          match pendSL lay lin a.indexMasks w X.NCL a.core with
          | none => .error "ROW: the shape"
          | some y => .ok (leaveAll ((a.setPile (a.pile ++ [y.1])).setCore y.2))
      else .ok (leaveAll a)
    else .error "cleared: the shape"
  | _, _ => .error "N: no link with its ledger is open"

/-- **THE TWO STEPS ARE ONE**, at all arguments. -/
theorem clearG_eq (X : LinkPub) (lay : WsLay) (lin : LinShape) (countsB : ChainSh → Bool)
    (leftSh : ChainSh → Option MergeSh) :
    clearG X lay lin countsB leftSh = clearGL X lay lin countsB leftSh := by
  funext a
  unfold clearG clearGL
  simp only [pendS_eq]
  rfl

/-- The step at a layers' link, light. -/
def clearLayGL (X : LinkPub) (lay : WsLay) (lin : LinShape) (NM : Nat) :
    ChainSh → Except String ChainSh := clearGL X lay lin (countsLayB NM) leftLaySh

/-- **It is the step at a layers' link.** -/
theorem clearLayG_eq (X : LinkPub) (lay : WsLay) (lin : LinShape) (NM : Nat) :
    clearLayG X lay lin NM = clearLayGL X lay lin NM := clearG_eq X lay lin _ _

/-- The step at the head's link, light. -/
def clearHeadGL (X : LinkPub) (lay : WsLay) (lin : LinShape) : ChainSh → Except String ChainSh :=
  clearGL X lay lin countsHeadB leftHeadSh

/-- **It is the step at the head's link.** -/
theorem clearHeadG_eq (X : LinkPub) (lay : WsLay) (lin : LinShape) :
    clearHeadG X lay lin = clearHeadGL X lay lin := clearG_eq X lay lin _ _

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.clearG_eq
#print axioms Johnson.AtFull.Shape.clearLayG_eq
#print axioms Johnson.AtFull.Shape.clearHeadG_eq
#print axioms Johnson.AtFull.Shape.clearGL
#print axioms Johnson.AtFull.Shape.clearLayGL
#print axioms Johnson.AtFull.Shape.clearHeadGL
