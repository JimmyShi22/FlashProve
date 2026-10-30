-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/CornerGround.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the prover's side: the hypothesis
CornerWorld (RowFields.lean) from the public facts K4Ground (Johnson/Road/K4/W/Ground.lean): the
world has 0 under every slot and the true entries; every table holds there what it says, so the
library's structures Fits and TrueAt3 hold there. Statements and proofs.

  `ptsPart_corner`        the verifier's list of points holds the point r_tV.
  **`cornerWorld_of_ground`**   CornerWorld.

Not shown here. That the hypotheses hold anywhere: no example is known. THAT THE PUBLIC FACTS
K4Ground HOLD AT A STRUCTURE OF HEARD VALUES WHOSE POINT r_tV IS A CORNER is a hypothesis: among
them, that the verifier's functions pointsOf and funsOf return there. That the tables which own the
places that the rows' forms name stand off the matrix of the lookup's planes (hOff) is a
hypothesis.
No property is claimed.
-/
import Johnson.Road.K4.C.RowFields
import Johnson.Road.K4.W.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Lay Ten Heard matIx TableAsk TableAt pointsOf)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell led bS)
open Blocks (ext)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Road.K4 (entryOf holds_entryOf)
open OnBytes.Road.K4.W (K4Ground ground uEOf)

/-- The verifier's list of points holds the point r_tV. -/
theorem ptsPart_corner {y : Lay} {H : Heard} {hd : Level} {hd2 : Option Level}
    {pts : List (String × Array E)} (h : pointsOf y H hd hd2 = some pts) :
    PtsPart [("r_tV", H.tV.r)] pts := by
  obtain ⟨_, _, _, _, _, h5⟩ := pointsOf_names3 h
  intro n q hq
  rw [List.find?_cons] at hq
  split at hq
  · rename_i hb
    obtain rfl := Option.some.inj hq
    obtain rfl : "r_tV" = n := eq_of_beq hb
    exact h5
  · cases hq

/-- **A WORLD WITH THE TRUE ENTRIES AT TOKEN i's CORNER**, from the public facts at heard values
whose point r_tV is the corner. -/
theorem cornerWorld_of_ground {h : Layer.Shape} {pc : List (List String)} {v : Env}
    {rd : Layer.Reads}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {tl : HTailF2} {H : Heard}
    {hd : Level} {hd2 : Option Level} {pts : List (String × Array E)} {funs : Array HFun}
    {D : Dim} (G : K4Ground h pc v rd r tl H hd hd2 pts funs D) {Q : K4Pub} (hy : v.y = Q.P.y)
    (Mm : Mats Cb.Gl.E) {i : ℕ} (hr : H.tV.r = cornerPt D.lT i)
    (hOff : ∀ fs, rowForms v = some fs → ∀ a ∈ fs.toList, ∀ x ∈ a.ents.toList,
      ∀ z : HFun × ℕ × ℕ, z.1 ∈ funs → tl.tabAt z.1 z.2.1 z.2.2 = some (x.row * v.K3 + x.idx) →
      z.1.mat ≠ (matIx Q.P.y).iB) :
    CornerWorld (scl := sclOf h v.sc v.g v.y.Lam) Q v tl r Mm D (cellsOf D (cellsAt v.y Mm)) i := by
  have hl := G.tables
  rw [← G.mats] at hl
  have hR := holds_entryOf Reading.gl (apart_of_run hl G.funs G.NM) v.iU3 v.K3 Mm
    (W := ⟨fun _ => 0, entryOf Reading.gl tl funs v.iU3 v.K3 Mm⟩) rfl
  obtain ⟨Z1, ZV, _, _, F, T3⟩ := ground G gl_numerals Mm hR
  rw [hr] at T3
  have hf := G.funs
  rw [hy] at hf
  have hp := ptsPart_corner G.points
  rw [hr] at hp
  exact ⟨_, funs, H.fo, pts, _, _, _, _, _, _, _, F, T3, rfl, fun _ => rfl, hf, hp, hOff⟩

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.ptsPart_corner
#print axioms OnBytes.Road.K4.C.cornerWorld_of_ground
