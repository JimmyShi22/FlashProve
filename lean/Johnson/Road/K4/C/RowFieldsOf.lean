-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/RowFieldsOf.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the prover's side: the hypothesis RowFields
(Norms.lean) from the public facts at ONE structure of heard values: the facts are carried to each
token's corner (GroundCorner.lean), there is a world at each corner (CornerGround.lean), and the
law on the honest reads does the rest (RowFields.lean). Statements and proofs.

  **`rowFields_of_ground`**   RowFields.

Not shown here. That the hypotheses hold anywhere: no example is known. That the public facts
K4Ground hold at the makers' own environment, that the plan's list of matrices and lists of points
are the layout's (hmQ, hrd), the cells (CellsAre), two numbers (hNI, hs), and that the tables which
own the places that the rows' forms name stand off the matrix of the lookup's planes (hOff) are
hypotheses; hOff follows from three public premises (rows_off, RowsBelow.lean). Nothing says that
the cells are those of an inference.
No property is claimed.
-/
import Johnson.Road.K4.C.GroundCorner

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Lay Ten Heard matIx TableAsk TableAt funsOf)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell led bS)
open Blocks (ext)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Road.K4.W (K4Ground)

/-- **THE FOUR FIELDS OF EACH NORM's ROW AT EACH TOKEN**, from the public facts at one structure of
heard values. v: the makers' own environment. hOff: at every list of tables that the verifier's
function funsOf makes of the laid families, at whatever list of points. -/
theorem rowFields_of_ground {h : Layer.Shape} {pc : List (List String)} {v : Env}
    {rd : Layer.Reads} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {tl : HTailF2}
    {H : Heard} {hd : Level} {hd2 : Option Level} {pts : List (String × Array E)}
    {funs : Array HFun} {D : Dim} (G : K4Ground h pc v rd r tl H hd hd2 pts funs D) {Q : K4Pub}
    {w : K4In} {p : Pts} (hv : OnBytes.Desc.First.K4.Honest.envOf Q p = some v)
    (hmQ : matsOf Q = matsR v.y v.g) (hrd : Q.P.rd = rd) {Mm : Mats Cb.Gl.E}
    (C : CellsAre Q w Mm) (hNI : Q.P.y.NI = D.nNu) (hs : H.tV.r.size = D.lT)
    (hOff : ∀ (pts' : List (String × Array E)) (funs' : Array HFun),
      funsOf Q.P.y H.fo pts' r.2.1 = some funs' → ∀ fs, rowForms v = some fs → ∀ a ∈ fs.toList,
      ∀ x ∈ a.ents.toList, ∀ z : HFun × ℕ × ℕ, z.1 ∈ funs' →
      tl.tabAt z.1 z.2.1 z.2.2 = some (x.row * v.K3 + x.idx) → z.1.mat ≠ (matIx Q.P.y).iB) :
    RowFields Q w p D (cellsOf D (cellsAt v.y Mm)) := by
  letI : Scl := sclOf h v.sc v.g v.y.Lam
  have hy := envOf_y hv
  have hg := envOf_g hv
  have hW := cornerWorld_all G hy Mm hs hOff
  have hlt : Q.P.y.h.lt = D.lT := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, F, _⟩ := hW 0
    rw [← hy]
    exact F.lT
  have hl := G.tables
  rw [← hmQ, hy, ← hrd, hg] at hl
  have hm := G.mats
  rw [← hmQ] at hm
  exact rowFields_read (scl := sclOf h v.sc v.g v.y.Lam) hv hl hm G.NM C hlt hNI fun i _ => hW i

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.rowFields_of_ground
