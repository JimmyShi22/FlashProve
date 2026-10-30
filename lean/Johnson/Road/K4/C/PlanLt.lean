-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/PlanLt.lean: CONDITIONAL.

What is here. A layout that the verifier's function `layout` has returned has at least four bits for
a token's number (`lt_of_layout`: its first half, `layoutBase`, OnBytes/Model/LayerLayout.lean,
returns an error at a shape with lt < 4, in its test on the shape's words); so under K4Plan the
plan's own layout has (`lt_of_plan`). Law/W/FitStack.lean calls it, so that neither that file nor
Law/W/FitStackPub.lean nor Law/MakersFitPlan.lean asks «lt is not 0». The two statements of
Law/W/FootJoin.lean still ask 1 ≤ lt (hlt) beside K4Plan: `lt_of_plan` would give it there; it is
not called. The steps follow the library's admitted_of_base (Johnson/Road/FormsKeysLaid.lean), which
reads the same test for ll and f.

  `lt_of_layout`   4 ≤ h.lt, for the shape h.
  `lt_of_plan`   4 ≤ P.y.h.lt, for the plan's layout.

Not shown here. That layout returns: a hypothesis of the first; a field of K4Plan in the second (ITS
FIELD sw BARS EVERY SHAPE BUT THOSE WITH THE LIBRARY's ELEVEN SWITCHES). Nothing on soundness, on
completeness or on any other property. No property is claimed.
-/
import Johnson.Road.K4.W.GroundOfHear
import Johnson.Road.FormsKeysLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Pub layout layoutBase)
open OnBytes.Road.K4.W (K4Plan)
open Inst.Model.FFSeg (Dim)

/-- **A layout that is returned has at least four bits for a token's number.** CONDITIONAL: on the
return. -/
theorem lt_of_layout {h : Layer.Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) : 4 ≤ h.lt := by
  unfold layout at hy
  obtain ⟨y0, h0, _⟩ := ok_of_bind hy
  unfold layoutBase at h0
  obtain ⟨-, h0⟩ := ok_of_refuse h0
  obtain ⟨e2, _⟩ := ok_of_refuse h0
  have a1 := or_false_split e2
  have a2 := or_false_split a1.1
  have a3 := or_false_split a2.1
  have a5 := or_false_split a3.1
  have a6 := or_false_split a5.1
  have a7 := or_false_split a6.1
  have a8 := or_false_split a7.1
  have a9 := or_false_split a8.1
  exact Nat.not_lt.mp (of_decide_eq_false a9.1)

/-- **So has the plan's own layout.** CONDITIONAL: on K4Plan. -/
theorem lt_of_plan {P : Pub} {g : ℕ} {hS : Layer.Shape} {pc : List (List String)} {tl : HTailF2}
    {D : Dim} (A : K4Plan hS pc P g tl D) : 4 ≤ P.y.h.lt := by
  rw [(admitted_of_layout A.lay A.sw.p3).shape]
  exact lt_of_layout A.lay

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.lt_of_layout
#print axioms OnBytes.Road.K4.C.lt_of_plan
