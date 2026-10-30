-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Back.lean: K05_port_top (Att/K05PortTop.lean) the other way round, and the
two as one equivalence.

Main names:
  `K05_port_top_back`: under the premises of K05_port_top but its two on worths: where the
    pull-backs of all claims of the library's ledger ownCl hold
    at the run made of what was heard, every gathered form is worth 0 and the join's form is worth
      0.
  `K05_port_iff`: under that one list of premises the two say the same.

So, of what stands behind the kind (GatheredTop, Att/K05RowTop.lean), the two conjuncts on worths
ask no more than the library's ledger does, where
the gathering returns, hjv holds and the late entries read off the world agree with their forms
(Cb.Sub.Agree).
Premises left: the gathering's returns; hjv; Agree; the public premises of K05_port_top.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05PortTop
import Johnson.Desc.First.Att.Claims.BackAll
import Johnson.Desc.First.Att.Claims.BackAt
import Johnson.Desc.First.Att.Claims.BackJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH UnitsClaims seenAfter recOf)
open VerifiableInference.Desc.Part
open K5Law (oldOf)
open OnBytes.Road (pt)
open Inst.Model.AttSeg (yn yi')
open Cb.Pv.Att.End (EndLay JoinLay Fits ownCl attA joinF)
open K5Law (PlanLaw AllZero)

variable {M0 Mg X : Type}

/-- **K05_port_top backwards.** -/
theorem K05_port_top_back (P0 : OwnPar Cb.Gl.E M0 X) (Λ : Lin P0 Mg) {G : Fork} {h : Heard} (hk4 : P0.kap = 4) (rows : ℕ)
    {L : Lists} (b2 : Said (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h G L) (b3 : Sized G) {S : Attention.Shape} {lid : ℕ}
    {cf : Attention.Cfg} {fs : Model.Forest.Shape} (hid : Attention.shapeHid lid cf = Except.ok (S, fs))
    (PL : PlanLaw cf S fs) (hDS : P0.D = OnBytes.Road.L5.dimOf S)
    (hC : P0.C = OnBytes.Road.L5.callsOf fs) (hnpl : P0.npl = 2) (hlt : S.cf.lt = P0.D.lT)
    (hNP : (geoOf S).NP = (size18 P0.D).pairs) {zx zy : Array E} {zk : Array (Array E)} (x0 : X)
    (H3 : K3Pts fs zx zy zk (P0.zOf x0)) {qW qM qD : Fin 4}
    (UW : ∀ wl, (geoOf S).single .wl = some wl → UnitIs P0.D P0.C .w3 qW wl)
    (UM : UnitIs P0.D P0.C .m1 qM ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fm)) (UD : UnitIs P0.D P0.C .d1 qD ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fd))
    (nz : BetasNz Reading.gl L) (du : UnitsH Reading.gl ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans Cb.Gl.E _ _ _)).units) (dt : TailH Reading.gl ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans Cb.Gl.E _ _ _)).tail)
    (d1 : UnitsOfP ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans Cb.Gl.E _ _ _)).units du (recOf (closedOf P0 Λ G.ns (numsOf h)) rows).score h.scores.toList L.planes.flatten L.units)
    (d2 : TailOfP dt (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h L)
    (d3 : UnitsVals ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans Cb.Gl.E _ _ _)).units du
      (unitsAdd (ρ := Reading.gl) ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans Cb.Gl.E _ _ _)).units (landedUnits _ _) L.planes.flatten L.units (x0, [])))
    (d4 : TailVals dt (tailAdd ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans Cb.Gl.E _ _ _)).tail L h nz (landedTail _ _) (seenAfter ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans Cb.Gl.E _ _ _)).units du (x0, []))))
    (cu : UnitsClaims ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans Cb.Gl.E _ _ _)).units du (x0, [])) (ct : dt.Claims (seenAfter ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans Cb.Gl.E _ _ _)).units du (x0, [])))
    {l : Left} (li : LeftIs (geoOf S) zk h G l) (m : Mg) (entry : ℕ → ℕ → ℕ → Cb.Gl.E)
    (A : Attention.Plan) (gL : Forest.Heard) {i : Runs.In} {Kc : ℕ} {l₁ l₂ : List Aff} {jn : Runs.JoinsP}
    (hg : i.g = geoOf S) (hz : i.zk = gL.zk) (hzk : gL.zk = zk) (hN : A.NC = S.calls.size)
    (hP : pointsOf i.g zk h l = some i.p) (h1 : Runs.firstRun i Kc = some (l₁, jn))
    (h2 : Runs.secondRun i Kc = some l₂)
    (hptM : (oldOf S gL i).t.ptM = Attention.pointM S (oldOf S gL i).d)
    (hptD : (oldOf S gL i).t.ptD = Attention.pointD S (oldOf S gL i).d)
    {k3 : Runs.PadIn} {kf : Array Aff} (hk : Runs.keysRun i k3 jn = some kf)
    {Fj : Fork} {tj : OnBytes.K.Kc.Tape} {xj : Aff × Fork × OnBytes.K.Kc.Tape}
    (hx : VerifiableInference.Desc.First.Look.joinF gL kf Fj tj = some xj)
    {J₂ : Type} [Fintype J₂] [DecidableEq J₂] {Ly : EndLay (closedOf P0 Λ G.ns (numsOf h)) J₂} {Q : JoinLay (closedOf P0 Λ G.ns (numsOf h))} (hFit : Fits Ly Q)
    (hls : Ly.ls = S.ls) (hlm : Ly.lmS = S.cf.lmS) (hscl : (Q.scl.κ 0).sh = S.cf.sh.getD 0 0)
    (hjv : ∀ kv, Cb.Pv.Att.End.joinVal (K5Law.qAt Reading.gl gL) kv (gL.cEnd.value Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry)) =
      Cb.Pv.Att.End.joinVal (Q.q x0) kv ((Q.ce x0).val ((closedOf P0 Λ G.ns (numsOf h)).msg m)))
    (hA : Cb.Sub.Agree (attA Ly (runHeard (closedOf P0 Λ G.ns (numsOf h)) x0 du dt)) ((closedOf P0 Λ G.ns (numsOf h)).msg m) (K5Law.uAt (G.worldOf Reading.gl (Λ.maskOf m) entry) (oldOf S gL i) Kc Ly.Y (OnBytes.Road.Rows.tabOfAtt (oldOf S gL i)) (OnBytes.Road.Rows.placeAtt S)))
    (Hcl : ∀ f ∈ ownCl Ly Q (runHeard (closedOf P0 Λ G.ns (numsOf h)) x0 du dt),
        (Cb.Sub.pullF (attA Ly (runHeard (closedOf P0 Λ G.ns (numsOf h)) x0 du dt)) f).Holds ((closedOf P0 Λ G.ns (numsOf h)).msg m)) :
    AllZero Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry) (l₁ ++ l₂) ∧
      xj.1.value Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry) = 0 := by
  have Nm := OnBytes.Road.gl_numerals
  have Ap : OnBytes.Road.Rows.AttPub Reading.gl (oldOf S gL i) lid cf fs := ⟨Nm, hid⟩
  have Nn := OnBytes.Road.Rows.norm_of_hid hid
  have Zs := OnBytes.Road.Rows.sizes_of_hid hid
  have PA := K5Law.points_are hP
  obtain ⟨lpW, lpM, lpD⟩ := lookAll_of_k3 P0 S PL.fit hC zk ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fm) ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fd) x0 H3 UW UM UD
  obtain ⟨Lk, hK⟩ := k3_look H3 ((closedOf P0 Λ G.ns (numsOf h)).pub0 (runHeard (closedOf P0 Λ G.ns (numsOf h)) x0 du dt).y0) rfl
  have hgs := K5Law.place_scores PL.place
  have hkr : i.g.units .kr [.rm, .rd] = [(0, callOf (OnBytes.Road.L5.callAt S 0), .rm),
      (0, callOf (OnBytes.Road.L5.callAt S 0), .rd)] := by rw [hg]; exact K5Law.place_kr PL.place
  have hgs' : i.g.scores = [((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fm), ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fd)] := by rw [hg]; exact hgs
  obtain ⟨a1, a2, k1, k2, ea1, ea2, ek1, ek2, It, I1, I2, close⟩ := K5Law.sayAt_back (ρ := Reading.gl)
    (W := (G.worldOf Reading.gl (Λ.maskOf m) entry)) (gL := gL) A hg hz hN hP h1 h2 Zs.G hkr hgs'
  have Pt0 := K5Law.pts_top (a1 := a1) (a2 := a2) hid PL Lk hK hg hz hP ek1 ek2 h1 hDS hC
  have Sl := slotsH_at P0 Λ rows b2 b3 S hDS hnpl nz x0 du dt d1 d2 d3 d4 cu ct m entry gL PA Ap
    (r1 := (0, callOf (OnBytes.Road.L5.callAt S 0), .rm)) (r2 := (0, callOf (OnBytes.Road.L5.callAt S 0), .rd))
    (u1 := ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fm)) (u2 := ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fd)) ea1 ea2 ek1 ek2 (K5Law.uAt (G.worldOf Reading.gl (Λ.maskOf m) entry) (oldOf S gL i) Kc Ly.Y (OnBytes.Road.Rows.tabOfAtt (oldOf S gL i)) (OnBytes.Road.Rows.placeAtt S))
  have Hh := K5Law.ownCl_of_pull_agree hA Hcl
  have Sl0 := Sl
  rw [← K5Law.sixTop_eq hg] at Sl0
  have hj := (K5Law.parts_of_ownCl Hh).2.2.2.2.2.2.1
  refine ⟨?_, K5Law.hj_top_back A hid PL Nm Lk hK hg hz hzk hN hP ea1 ea2 ek1 ek2 h1 hk hDS hC hnpl hscl Sl0 hjv hx hj⟩
  have Pt := Pt0
  rw [K5Law.sixTop_eq hg] at Pt
  have vn := Pt0.dv.vnW
  have vi := vi_of (ρ := Reading.gl) gL hg hP Nn (Nat.le_of_succ_le Zs.lnT) (C := P0.C) (z := P0.zOf x0)
    (by rw [← hDS]; exact lpW)
  have hzi := (K5Law.pub_a (gL := gL) hg (K5Law.points_more hP)).zi
  have O := outs_are (closedOf P0 Λ G.ns (numsOf h)) gL rows hDS hk4 Nn (Nat.le_of_succ_le Zs.lnT) hg hP hptM hptD b2 x0 du dt d1 d2 cu ct ek1 ek2
    (K5Law.sixAt i.g zk (0, callOf (OnBytes.Road.L5.callAt S 0), .rm) (0, callOf (OnBytes.Road.L5.callAt S 0), .rd) a1 a2 k1 k2 ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fm) ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fd)) rfl rfl vn vi hzi
  obtain ⟨f1, f2, hfs, R8⟩ := rows_core P0 Λ hk4 rows b2 b3 S hDS Zs hlt hNP hgs (K5Law.below_fm _).1 (K5Law.below_fm _).2 nz
    x0 lpW lpM lpD du dt d1 d2 d3 d4 cu ct li m entry
  have Rh := K5Law.rowsHold_back Hh
  have Zz : K5Law.SizesAre (closedOf P0 Λ G.ns (numsOf h)) Ly (oldOf S gL i) := ⟨hDS, hk4, hls, hlm⟩
  obtain ⟨sVM, sVD⟩ := vp_sizes (closedOf P0 Λ G.ns (numsOf h)) gL rows hDS (Nat.le_of_succ_le Zs.lnT) hP b2 dt d2
  have Nn' := K5Law.shape_nums Zz Ap hptM hptD sVM sVD hzi
  have er := K5Law.rows_are PA
  rw [hfs] at er
  have er1 : k1.sc.row = f1 := by
    have e := congrArg (·[0]?) er
    simp only [List.getElem?_map, Array.getElem?_toList, ek1, Option.map_some, List.getElem?_cons_zero,
      Option.some.injEq] at e
    exact e
  have er2 : k2.sc.row = f2 := by
    have e := congrArg (·[1]?) er
    simp only [List.getElem?_map, Array.getElem?_toList, ek2, Option.map_some, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Option.some.injEq] at e
    exact e
  have RZ : K5Law.RowsZero Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry) (oldOf S gL i)
      (K5Law.sixAt i.g zk (0, callOf (OnBytes.Road.L5.callAt S 0), .rm) (0, callOf (OnBytes.Road.L5.callAt S 0), .rd) a1 a2 k1 k2 ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fm) ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fd)) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show k1.sc.row.value Reading.gl _ = 0
      rw [er1]
      exact R8.rM.2 Rh.rM
    · show k2.sc.row.value Reading.gl _ = 0
      rw [er2]
      exact R8.rD.2 Rh.rD
    · show i.p.d.scE.row.value Reading.gl _ = 0
      rw [PA.scE]
      exact R8.rE.2 Rh.rE
    · show i.p.d.vpm.row.value Reading.gl _ = 0
      rw [PA.vpm]
      exact R8.rVM.2 Rh.rVM
    · show i.p.d.vpd.row.value Reading.gl _ = 0
      rw [PA.vpd]
      exact R8.rVD.2 Rh.rVD
    · show i.p.x.scF.row.value Reading.gl _ = 0
      rw [PA.scF]
      exact R8.rF.2 Rh.rF
    · show i.p.x.scd.row.value Reading.gl _ = 0
      rw [PA.scd]
      exact R8.rK.2 Rh.rK
    · show i.p.x.scH.row.value Reading.gl _ = 0
      rw [PA.scH]
      exact R8.rH.2 Rh.rH
  obtain ⟨sM, sD, uM, uD, s5, s6, s7, s8⟩ := K5Law.say_back _ Zz Ap hFit Nn' It I1 I2 rfl rfl rfl rfl rfl rfl Pt O Sl RZ Hh
  exact close sM sD uM uD s5 s6 s7 s8

/-- **The two say the same**: under the gathering's returns, hjv and Agree (and K05_port_top's
public premises): every gathered
form is worth 0 and the join's form is worth 0, if and only if the pull-backs of all claims of the
library's ledger hold. -/
theorem K05_port_iff (P0 : OwnPar Cb.Gl.E M0 X) (Λ : Lin P0 Mg) {G : Fork} {h : Heard} (hk4 : P0.kap = 4) (rows : ℕ)
    {L : Lists} (b2 : Said (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h G L) (b3 : Sized G) {S : Attention.Shape} {lid : ℕ}
    {cf : Attention.Cfg} {fs : Model.Forest.Shape} (hid : Attention.shapeHid lid cf = Except.ok (S, fs))
    (PL : PlanLaw cf S fs) (hDS : P0.D = OnBytes.Road.L5.dimOf S)
    (hC : P0.C = OnBytes.Road.L5.callsOf fs) (hnpl : P0.npl = 2) (hlt : S.cf.lt = P0.D.lT)
    (hNP : (geoOf S).NP = (size18 P0.D).pairs) {zx zy : Array E} {zk : Array (Array E)} (x0 : X)
    (H3 : K3Pts fs zx zy zk (P0.zOf x0)) {qW qM qD : Fin 4}
    (UW : ∀ wl, (geoOf S).single .wl = some wl → UnitIs P0.D P0.C .w3 qW wl)
    (UM : UnitIs P0.D P0.C .m1 qM ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fm)) (UD : UnitIs P0.D P0.C .d1 qD ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fd))
    (nz : BetasNz Reading.gl L) (du : UnitsH Reading.gl ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans Cb.Gl.E _ _ _)).units) (dt : TailH Reading.gl ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans Cb.Gl.E _ _ _)).tail)
    (d1 : UnitsOfP ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans Cb.Gl.E _ _ _)).units du (recOf (closedOf P0 Λ G.ns (numsOf h)) rows).score h.scores.toList L.planes.flatten L.units)
    (d2 : TailOfP dt (recOf (closedOf P0 Λ G.ns (numsOf h)) rows) h L)
    (d3 : UnitsVals ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans Cb.Gl.E _ _ _)).units du
      (unitsAdd (ρ := Reading.gl) ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans Cb.Gl.E _ _ _)).units (landedUnits _ _) L.planes.flatten L.units (x0, [])))
    (d4 : TailVals dt (tailAdd ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans Cb.Gl.E _ _ _)).tail L h nz (landedTail _ _) (seenAfter ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans Cb.Gl.E _ _ _)).units du (x0, []))))
    (cu : UnitsClaims ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans Cb.Gl.E _ _ _)).units du (x0, [])) (ct : dt.Claims (seenAfter ((closedOf P0 Λ G.ns (numsOf h)).own (theMeans Cb.Gl.E _ _ _)).units du (x0, [])))
    {l : Left} (li : LeftIs (geoOf S) zk h G l) (m : Mg) (entry : ℕ → ℕ → ℕ → Cb.Gl.E)
    (A : Attention.Plan) (gL : Forest.Heard) {i : Runs.In} {Kc : ℕ} {l₁ l₂ : List Aff} {jn : Runs.JoinsP}
    (hg : i.g = geoOf S) (hz : i.zk = gL.zk) (hzk : gL.zk = zk) (hN : A.NC = S.calls.size)
    (hP : pointsOf i.g zk h l = some i.p) (h1 : Runs.firstRun i Kc = some (l₁, jn))
    (h2 : Runs.secondRun i Kc = some l₂)
    (hptM : (oldOf S gL i).t.ptM = Attention.pointM S (oldOf S gL i).d)
    (hptD : (oldOf S gL i).t.ptD = Attention.pointD S (oldOf S gL i).d)
    {k3 : Runs.PadIn} {kf : Array Aff} (hk : Runs.keysRun i k3 jn = some kf)
    {Fj : Fork} {tj : OnBytes.K.Kc.Tape} {xj : Aff × Fork × OnBytes.K.Kc.Tape}
    (hx : VerifiableInference.Desc.First.Look.joinF gL kf Fj tj = some xj)
    {J₂ : Type} [Fintype J₂] [DecidableEq J₂] {Ly : EndLay (closedOf P0 Λ G.ns (numsOf h)) J₂} {Q : JoinLay (closedOf P0 Λ G.ns (numsOf h))} (hFit : Fits Ly Q)
    (hls : Ly.ls = S.ls) (hlm : Ly.lmS = S.cf.lmS) (hscl : (Q.scl.κ 0).sh = S.cf.sh.getD 0 0)
    (hjv : ∀ kv, Cb.Pv.Att.End.joinVal (K5Law.qAt Reading.gl gL) kv (gL.cEnd.value Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry)) =
      Cb.Pv.Att.End.joinVal (Q.q x0) kv ((Q.ce x0).val ((closedOf P0 Λ G.ns (numsOf h)).msg m)))
    (hA : Cb.Sub.Agree (attA Ly (runHeard (closedOf P0 Λ G.ns (numsOf h)) x0 du dt)) ((closedOf P0 Λ G.ns (numsOf h)).msg m) (K5Law.uAt (G.worldOf Reading.gl (Λ.maskOf m) entry) (oldOf S gL i) Kc Ly.Y (OnBytes.Road.Rows.tabOfAtt (oldOf S gL i)) (OnBytes.Road.Rows.placeAtt S))) :
    (AllZero Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry) (l₁ ++ l₂) ∧
      xj.1.value Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry) = 0) ↔
    ∀ f ∈ ownCl Ly Q (runHeard (closedOf P0 Λ G.ns (numsOf h)) x0 du dt),
        (Cb.Sub.pullF (attA Ly (runHeard (closedOf P0 Λ G.ns (numsOf h)) x0 du dt)) f).Holds ((closedOf P0 Λ G.ns (numsOf h)).msg m) :=
  ⟨fun hh => K05_port_top P0 Λ hk4 rows b2 b3 hid PL hDS hC hnpl hlt hNP x0 H3 UW UM UD nz du dt d1 d2 d3 d4 cu ct li m entry A gL hg hz hzk hN hP h1 h2 hh.1 hptM hptD hk hx hh.2 hFit hls hlm hscl hjv hA,
    fun Hcl => K05_port_top_back P0 Λ hk4 rows b2 b3 hid PL hDS hC hnpl hlt hNP x0 H3 UW UM UD nz du dt d1 d2 d3 d4 cu ct li m entry A gL hg hz hzk hN hP h1 h2 hptM hptD hk hx hFit hls hlm hscl hjv hA Hcl⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_port_top_back
#print axioms VerifiableInference.Desc.First.Att.P.K05_port_iff
