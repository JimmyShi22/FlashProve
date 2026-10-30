-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Port.lean: port_pull (Att/Claims/PortAll.lean) at the closed parameters,
the run made of what was heard
and the record oldOf S gL i of OnBytes/Model: from "every gathered form is worth 0" to the
pull-backs of all claims of the
library's ledger ownCl at that run.

Main names:
  `rows_hold`: the eight rows' claims hold: rows_core (Att/K05Rows.lean) and "the rows are worth 0"
    (tail_rows, unit_at).
  `K05_port`.

The ledger G is any with Said and Sized: so also a later one than the ledger right behind the
hearing (Said.mono).
Paid inside: SizesAre, ShapeNums, Say, InTail, SixSay, OutsAre, RowsHold.
Premises left: Fits; AttPub; PtsAre (the points and the weights at the lookup's end point); SlotsH
(the dictionary of
slots); the join (joinF); Agree (each late entry of the world is its table's meant value: "the
tables are true"); the two
runs' return and AllZero; pointsOf's return; the two points' texts; two ties of the lookup's inner
point; facts of the
plan (two remainder-table units; two softmax-table units, the first below the diagonal); and the
premises of rows_core.
None of these is shown in this file or in what it imports.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05OutsAre
import Johnson.Desc.First.Att.K05Fits

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH UnitsClaims seenAfter recOf)
open VerifiableInference.Desc.Part
open K5Law (oldOf PointsAre points_are SayAt tail_rows unit_at RowsHold AllZero say_at units_visited six_say say_tail_at
  shape_nums sixAt PtsAre SlotsH uAt port_pull pub_a points_more SizesAre)
open Cb.Pv.Att.End (EndLay JoinLay Fits ownCl attA joinF)
open OnBytes.Road (pt)
open OnBytes.Road.Rows (AttPub norm_of_hid sizes_of_hid tabOfAtt placeAtt)
open Inst.Model.AttSeg (yn yi')

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M0 Mg X : Type}

/-- **The eight rows' claims hold**, where K5's gathered claims say so. -/
theorem rows_hold {P : OwnPar K Mg X} {u : P.Run} {f1 f2 : Aff} {l : Left} {W : World K} {m : Mg}
    (R : Rows8 (ρ := ρ) P u f1 f2 l W m) (hfs : l.scores.toList = [f1, f2]) {S : Attention.Shape} {gL : Forest.Heard}
    {i : Runs.In} {Kc : ℕ} {zk : Array (Array E)} {h : Heard} (H : PointsAre i.g zk h l i.p)
    (Sy : SayAt ρ W S gL i Kc) {o1 o2 : ℕ × MaskedSum.Heard} (hos : h.scores.toList = [o1, o2]) : RowsHold P u m := by
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := tail_rows H Sy
  obtain ⟨_, g1, _, e1, _, _, z1, _⟩ := unit_at H Sy 0 o1 (by rw [← Array.getElem?_toList, hos]; rfl)
  obtain ⟨_, g2, _, e2, _, _, z2, _⟩ := unit_at H Sy 1 o2 (by rw [← Array.getElem?_toList, hos]; rfl)
  rw [← Array.getElem?_toList, hfs] at e1 e2
  obtain rfl : f1 = g1 := Option.some.inj e1
  obtain rfl : f2 = g2 := Option.some.inj e2
  exact ⟨R.rM.1 z1, R.rD.1 z2, R.rE.1 t1, R.rVM.1 t2, R.rVD.1 t3, R.rF.1 t4, R.rK.1 t5, R.rH.1 t6⟩

/-- **From «every gathered form is worth 0» to the left side of LeadsSaysCl's last clause.** -/
theorem K05_port (P0 : OwnPar K M0 X) (Λ : Lin P0 Mg) {G : Fork} {h : Heard} (hk4 : P0.kap = 4) (rows : ℕ) {L : Lists}
    (b2 : Said (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h G L) (b3 : Sized G) (S : Attention.Shape)
    (hDS : P0.D = OnBytes.Road.L5.dimOf S) (hlt : S.cf.lt = P0.D.lT) (hNP : (geoOf S).NP = (size18 P0.D).pairs)
    {u1 u2 : UnitG} (hgs : (geoOf S).scores = [u1, u2]) (hb1 : u1.below = true) (hb2 : u2.below = false)
    {zk : Array (Array E)} (nz : BetasNz ρ L) (x0 : X)
    (lpW : ∀ wl, (geoOf S).single .wl = some wl → LookPts ρ P0.D P0.C (P0.zOf x0)
      (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[])))
    (lpM : UnitPtsM ρ P0.D P0.C (P0.zOf x0) u1 (zk.getD u1.call #[]))
    (lpD : UnitPtsD ρ P0.D P0.C (P0.zOf x0) u2 (zk.getD u2.call #[]))
    (du : UnitsH ρ ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units) (dt : TailH ρ ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).tail)
    (d1 : UnitsOfP ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units du (recOf (closedOf P0 Λ G.ns (numsOf h)) rows).score h.scores.toList L.planes.flatten L.units)
    (d2 : TailOfP dt (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h L)
    (d3 : UnitsVals ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units du
      (unitsAdd (ρ := ρ) ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units (landedUnits _ _) L.planes.flatten L.units (x0, [])))
    (d4 : TailVals dt (tailAdd ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).tail L h nz (landedTail _ _) (seenAfter ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units du (x0, []))))
    (cu : UnitsClaims ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units du (x0, [])) (ct : dt.Claims (seenAfter ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans K _ _ _)).units du (x0, [])))
    {l : Left} (li : LeftIs (geoOf S) zk h G l) (m : Mg) (entry : ℕ → ℕ → ℕ → K)
    (A : Attention.Plan) (gL : Forest.Heard) {i : Runs.In} {Kc : ℕ} {l₁ l₂ : List Aff} {jn : Runs.JoinsP}
    (hg : i.g = geoOf S) (hz : i.zk = gL.zk) (hN : A.NC = S.calls.size) (hP : pointsOf i.g zk h l = some i.p)
    (h1 : Runs.firstRun i Kc = some (l₁, jn)) (h2 : Runs.secondRun i Kc = some l₂)
    (hZ : AllZero ρ (G.worldOf ρ (Λ.maskOf m) entry) (l₁ ++ l₂)) (hG : S.G = 2 ^ S.cf.lgk)
    {r1 r2 : ℕ × CallG × Keys} (hkr : i.g.units .kr [.rm, .rd] = [r1, r2])
    {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape} (Ap : AttPub ρ (oldOf S gL i) lid cf fs)
    (hptM : (oldOf S gL i).t.ptM = Attention.pointM S (oldOf S gL i).d)
    (hptD : (oldOf S gL i).t.ptD = Attention.pointD S (oldOf S gL i).d)
    (vn : ∀ j < S.cf.ldh, pt ρ (oldOf S gL i).d.zcW j = yn P0.D P0.C (P0.zOf x0) j)
    (vi : ∀ j < S.cf.lB, pt ρ ((oldOf S gL i).d.zilo S) j = yi' (OnBytes.Road.L5.dimOf S) P0.C (P0.zOf x0) j)
    {J₂ : Type} [Fintype J₂] [DecidableEq J₂] {Ly : EndLay (closedOf P0 Λ G.ns (numsOf h)) J₂} {Q : JoinLay (closedOf P0 Λ G.ns (numsOf h))} (hFit : Fits Ly Q)
    (hls : Ly.ls = S.ls) (hlm : Ly.lmS = S.cf.lmS)
    (hPt : ∀ a1 a2 k1 k2, h.remainders[0]? = some a1 → h.remainders[1]? = some a2 → i.p.scores[0]? = some k1 →
      i.p.scores[1]? = some k2 →
      PtsAre ρ (oldOf S gL i) (closedOf P0 Λ G.ns (numsOf h)) (runHeard (closedOf P0 Λ G.ns (numsOf h)) x0 du dt) (sixAt i.g zk r1 r2 a1 a2 k1 k2 u1 u2) ∧
      SlotsH (G.worldOf ρ (Λ.maskOf m) entry) (oldOf S gL i) (closedOf P0 Λ G.ns (numsOf h)) (runHeard (closedOf P0 Λ G.ns (numsOf h)) x0 du dt) m
        (sixAt i.g zk r1 r2 a1 a2 k1 k2 u1 u2)
        (uAt (G.worldOf ρ (Λ.maskOf m) entry) (oldOf S gL i) Kc Ly.Y (tabOfAtt (oldOf S gL i)) (placeAtt S)))
    (hj : (joinF (J₂ := J₂) Q (runHeard (closedOf P0 Λ G.ns (numsOf h)) x0 du dt)).Holds (Sum.elim ((closedOf P0 Λ G.ns (numsOf h)).msg m)
      (uAt (G.worldOf ρ (Λ.maskOf m) entry) (oldOf S gL i) Kc Ly.Y (tabOfAtt (oldOf S gL i)) (placeAtt S))))
    (hA : Cb.Sub.Agree (attA Ly (runHeard (closedOf P0 Λ G.ns (numsOf h)) x0 du dt)) ((closedOf P0 Λ G.ns (numsOf h)).msg m)
      (uAt (G.worldOf ρ (Λ.maskOf m) entry) (oldOf S gL i) Kc Ly.Y (tabOfAtt (oldOf S gL i)) (placeAtt S))) :
    ∀ f ∈ ownCl Ly Q (runHeard (closedOf P0 Λ G.ns (numsOf h)) x0 du dt),
      (Cb.Sub.pullF (attA Ly (runHeard (closedOf P0 Λ G.ns (numsOf h)) x0 du dt)) f).Holds ((closedOf P0 Λ G.ns (numsOf h)).msg m) := by
  have N := norm_of_hid Ap.shape
  have Zs := sizes_of_hid Ap.shape
  have H := points_are hP
  have hgs' : i.g.scores = [u1, u2] := by rw [hg]; exact hgs
  have SyA := (say_at K ρ _ A S gL i Kc l₁ l₂ jn hg hz hN (units_visited H) h1 h2).1 hZ
  obtain ⟨Sy, It⟩ := say_tail_at (gL := gL) A hg hz hN h1 h2 hZ hG
  obtain ⟨a1, a2, k1, k2, ea1, ea2, ek1, ek2, S6⟩ := six_say (gL := gL) A hg hz hN hP h1 h2 hZ hG hkr hgs'
  obtain ⟨Pt, Sl⟩ := hPt a1 a2 k1 k2 ea1 ea2 ek1 ek2
  have hzi := (pub_a (gL := gL) hg (points_more hP)).zi
  have O := outs_are (closedOf P0 Λ G.ns (numsOf h)) gL rows hDS hk4 N (Nat.le_of_succ_le Zs.lnT) hg hP hptM hptD b2 x0 du dt d1 d2 cu ct ek1 ek2
    (sixAt i.g zk r1 r2 a1 a2 k1 k2 u1 u2) rfl rfl vn vi hzi
  obtain ⟨f1, f2, hfs, R8⟩ := rows_core P0 Λ hk4 rows b2 b3 S hDS Zs hlt hNP hgs hb1 hb2 nz x0 lpW lpM lpD du dt d1 d2
    d3 d4 cu ct li m entry
  obtain ⟨o1, o2, _, _, _, _, hos, _, _, _⟩ := units_two b2.units
  have Rh := rows_hold R8 hfs H SyA hos
  have Zz : SizesAre (closedOf P0 Λ G.ns (numsOf h)) Ly (oldOf S gL i) := ⟨hDS, hk4, hls, hlm⟩
  obtain ⟨sVM, sVD⟩ := vp_sizes (closedOf P0 Λ G.ns (numsOf h)) gL rows hDS (Nat.le_of_succ_le Zs.lnT) hP b2 dt d2
  have Nn := shape_nums Zz Ap hptM hptD sVM sVD hzi
  exact port_pull _ Zz Ap hFit Nn Sy S6 It Pt O Sl Rh hj hA

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_port
#print axioms VerifiableInference.Desc.First.Att.P.rows_hold
