-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/Ends.lean: CONDITIONAL.

Not shown here. THAT A FORM IS WORTH 0 ANYWHERE. That "every table holds" in a world: a hypothesis
here (W/Ground.lean proves it at one world: holds_item). Nothing on soundness, on completeness or on
any other property.

The library's structure EndGround (Johnson/Road/Rows/GatedEnds.lean), on which the end claims of the
two product layers of the gated products are read, from the public hypotheses of W/Ground.lean and
"every table holds what it says of Mm".

  `end_true`   a true long table at the last coordinates of a point, read at the point's own
      coordinates.
  `ground_ends`   EndGround at the first product layer's point hd.r and the tables "af@Z_a", and at
      the second product layer's point o2.r and the tables "af@Z_b".
No property is claimed.
-/
import Johnson.Road.K4.W.Ground
import Johnson.Road.K4.TrueAt4
import Johnson.Road.K4.ReadsThere2

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Lay Reads Heard Pub Own TableAsk TableAt Ten)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell lF lFe)
open OnBytes.Road.Rows (EndGround)

variable {K : Type} [Field K] {ρ : Reading K} {W : World K}

/-- A true long table at the last ls + lT coordinates of the point z, at z's own coordinates. -/
theorem end_true {v : Env} {tb mat lT g la : ℕ} {c : Cells K} {z Z : Array E}
    (hZ : lastOf z la = .ok Z) (hla : la = v.y.ls + lT) (hs : z.size = g + v.y.ls + lT)
    (h : LongTrue ρ W v tb mat v.y.ls lT c (pt ρ Z) (fun j => pt ρ Z (v.y.ls + j))) :
    LongTrue ρ W v tb mat v.y.ls lT c (fun j => pt ρ z (g + j))
      (fun j => pt ρ z (g + v.y.ls + j)) := by
  have eg : z.size - la = g := by omega
  refine Desc.First.K4.longTrue_congr (fun j hj => ?_) (fun j hj => ?_) h
  · rw [(Desc.First.K4.lastOf_pt (ρ := ρ) hZ (j := j) (by omega)).2, eg]
  · rw [(Desc.First.K4.lastOf_pt (ρ := ρ) hZ (j := v.y.ls + j) (by omega)).2, eg, Nat.add_assoc]

variable {h : Layer.Shape} {pc : List (List String)} {v : Env} {rd : Reads}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {tl : HTailF2} {H : Heard} {hd : Level}
  {hd2 : Option Level} {pts : List (String × Array E)} {funs : Array HFun} {D : Dim} {P : Pub}

/-- **EndGround at the two product layers' points.** CONDITIONAL: on G, Z, hρ, hR; and on h2 (there
is a second product layer: the half on hd.r asks it too), hts, htu, hA, hB (the verifier finds the
tensors "s" and "u" and the tables "af@Z_a" and "af@Z_b"). -/
theorem ground_ends (G : K4Ground h pc v rd r tl H hd hd2 pts funs D) (Z : K4Sizes P v H hd hd2 D)
    (hρ : Numerals ρ) (Mm : Mats K) (hR : ∀ Fn ∈ funs, Holds ρ W tl v.iU3 v.K3 Mm Fn)
    {o2 : Level} (h2 : hd2 = some o2) {ts tu : Ten} {tbA tbB : ℕ} (hts : v.y.T_ "s" = some ts)
    (htu : v.y.T_ "u" = some tu) (hA : v.tabAt "af@Z_a" = some tbA)
    (hB : v.tabAt "af@Z_b" = some tbB) :
    EndGround ρ W v D (cellsAt v.y Mm) (cellsOf D (cellsAt v.y Mm)) hd.r (D.lL + lF D - v.y.ls)
      tbA ts tu ∧
    EndGround ρ W v D (cellsAt v.y Mm) (cellsOf D (cellsAt v.y Mm)) o2.r
      (D.lL - 1 + lFe D - v.y.ls) tbB ts tu := by
  subst h2
  letI : Scl := sclOf h v.sc v.g v.y.Lam
  obtain ⟨Z1, ZV, _, _, F, _⟩ := ground G hρ Mm hR
  obtain ⟨ZA, ZB, hZA, hZB, T4⟩ := trueAt4_of_holds ρ W G.lay G.sw G.grp G.reads G.tables G.tab
    G.mats G.NM G.points G.funs Mm hR
  rw [F.lT] at T4
  have A := admitted_of_layout G.lay G.sw.p3
  have S : Switches v.y.h := by
    rw [A.shape]
    exact G.sw
  obtain ⟨tS, _, hS, tiedS, _, wholeS⟩ := F.long .sl rfl
  obtain ⟨tU, _, hU, tiedU, _, wholeU⟩ := F.long .up rfl
  obtain rfl : tS = ts := Option.some.inj ((tensorAt_T hS).symm.trans hts)
  obtain rfl : tU = tu := Option.some.inj ((tensorAt_T hU).symm.trans htu)
  have mS : tS.mat = 0 := (ten_facts A.laid S .sl rfl hts).1
  have mU : tU.mat = 0 := (ten_facts A.laid S .up rfl htu).1
  have tA := end_true hZA Z.la Z.hd (T4.afA _ hA)
  have tB := end_true hZB Z.la (Z.hd2 o2 rfl) (T4.afB _ hB)
  exact
    ⟨{ num := hρ
       S2 := F.S2
       size := Z.hd
       tiedS := tiedS
       tiedU := tiedU
       wholeS := wholeS
       wholeU := wholeU
       trueS := by rw [mS]; exact tA
       trueU := by rw [mU]; exact tA },
     { num := hρ
       S2 := F.S2
       size := Z.hd2 o2 rfl
       tiedS := tiedS
       tiedU := tiedU
       wholeS := wholeS
       wholeU := wholeU
       trueS := by rw [mS]; exact tB
       trueU := by rw [mU]; exact tB }⟩

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.end_true
#print axioms OnBytes.Road.K4.W.ground_ends
