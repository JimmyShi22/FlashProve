-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/RowFieldsTop.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the prover's side: the hypothesis RowFields
(Norms.lean) with hOff paid: rowFields_of_ground (RowFieldsOf.lean) fed by rows_off
(RowsBelow.lean). Statement and proof.

  **`rowFields_top`**   RowFields.

Not shown here. That the hypotheses hold anywhere: no example is known. That the public facts
K4Ground hold at the makers' own environment, that the plan's list of matrices and lists of points
are the layout's (hmQ, hrd), the cells (CellsAre), two numbers (hNI, hs) and that the family
"b-bits-0" has a place (hB) are hypotheses. Nothing says that the cells are those of an inference.
No property is claimed.
-/
import Johnson.Road.K4.C.RowFieldsOf
import Johnson.Road.K4.C.RowsBelow

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Lay Ten Heard matIx TableAsk TableAt)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell led bS)
open Blocks (ext)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Road.K4.W (K4Ground)

/-- **THE FOUR FIELDS OF EACH NORM's ROW AT EACH TOKEN**, from the public facts at one structure of
heard values. v: the makers' own environment. CONDITIONAL: on every hypothesis named. -/
theorem rowFields_top {h : Layer.Shape} {pc : List (List String)} {v : Env} {rd : Layer.Reads}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {tl : HTailF2} {H : Heard}
    {hd : Level} {hd2 : Option Level} {pts : List (String × Array E)} {funs : Array HFun}
    {D : Dim} (G : K4Ground h pc v rd r tl H hd hd2 pts funs D) {Q : K4Pub} {w : K4In} {p : Pts}
    (hv : OnBytes.Desc.First.K4.Honest.envOf Q p = some v) (hmQ : matsOf Q = matsR v.y v.g)
    (hrd : Q.P.rd = rd) {Mm : Mats Cb.Gl.E} (C : CellsAre Q w Mm) (hNI : Q.P.y.NI = D.nNu)
    (hs : H.tV.r.size = D.lT) {tB0 : ℕ} (hB : v.tabAt "b-bits-0" = some tB0) :
    RowFields Q w p D (cellsOf D (cellsAt v.y Mm)) := by
  have hl := G.tables
  rw [← hmQ, envOf_y hv, ← hrd, envOf_g hv] at hl
  exact rowFields_of_ground G hv hmQ hrd C hNI hs (rows_off hl G.tab hB H.fo)

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.rowFields_top
