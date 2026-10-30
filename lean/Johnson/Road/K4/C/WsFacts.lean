-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/WsFacts.lean: CONDITIONAL.

What is here. Six public facts that tie the shape of the committed matrix of weights to the layer
sub-proof's layout, and one equation on the bits of a token's number (`ws_facts`): the widths d and
fe are equal; the width of all query heads, the inner width of a dense layer and the number of
experts in the weights' shape are at most the layout's; an expert's width in the weights' shape is
at most the layout's inner width of a DENSE layer; the layout's lt is the parameters' lT. They are
the public hypotheses of `panel_units` (Johnson/Road/K4/C/UnitsOfClaim.lean). From two ties to one
set of the library's parameters: the plan's (`K4Plan`'s field sized,
Johnson/Road/K4/W/GroundOfHear.lean) and the weights' (`SizedW`, Johnson/Road/FormsKeysWLay.lean),
with the library's plain facts on a layout that `layout` returns (`admitted_of_layout`,
Johnson/Road/FormsKeysLaid.lean).

  `ws_facts`   the seven.

Not shown here. K4Plan and SizedW: hypotheses. WHERE K4Plan HOLDS: the head of
Johnson/Road/K4/W/GroundOfHear.lean; its field sw bars every shape but those with the library's
eleven switches. That the two hold together: under the library's head at the full size
(Johnson/Desc/ProofFile/Honest/K4/Law/W/WsFactsHead.lean); elsewhere no example is known. Nothing on
soundness, on completeness or on any other property. No property is claimed.
-/
import Johnson.Road.K4.W.GroundOfHear
import Johnson.Road.FormsKeysWLay
import Johnson.Road.FormsKeysLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Road.K4.W (K4Plan)
open Inst.Model.FFSeg (Dim)

/-- **The weights' shape against the layout.** CONDITIONAL: on A and Zw. -/
theorem ws_facts {hS : Layer.Shape} {pc : List (List String)} {P : Layer.Pub} {g : ℕ}
    {tl : HTailF2} {D : Dim} (A : K4Plan hS pc P g tl D) {s : WsShape} (Zw : SizedW s D.P) :
    s.d = P.y.h.d ∧ s.fe = P.y.h.fe ∧ s.dq ≤ P.y.dq ∧ s.f ≤ P.y.h.f ∧ s.fe ≤ P.y.h.f ∧
      s.NE ≤ P.y.h.NE ∧ P.y.h.lt = D.lT := by
  have Ad := admitted_of_layout A.lay A.sw.p3
  have Z := A.sized
  have e := Ad.shape
  refine ⟨by rw [Zw.d, Z.d, e], by rw [Zw.fe, Z.fe, e],
    Nat.le_of_eq (by rw [Zw.dq, Z.nq, Z.ch, Ad.laid.dq, e]), Nat.le_of_eq (by rw [Zw.f, Z.f, e]),
    ?_, Nat.le_of_eq (by rw [Zw.NE, Z.nexp, e]), by rw [e, Z.lT]⟩
  rw [Zw.fe, Z.fe, Ad.laid.ffe, e]
  omega

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.ws_facts
