-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05PortTop.lean: K05_port (Att/K05Port.lean) with its public premises paid,
at the field GE and the reading
Reading.gl.

Main names:
  `k3_look`: one fact of the lookup's kind for both records called LookAll: K3Pts
    (Att/K05LookAll.lean) gives the record LookAll
    of Att/Claims/LookKeys.lean and KeyIs at the four calls; by lookAll_of_k3 it gives the LookAll
      of Att/K05Cap.lean too.
  `points_ziW`, `vi_of`: the low part of the position in the inner point of the unit "wl", against
    yi': from LookPts.
  `K05_port_top`: the pull-backs of all claims of the library's ledger ownCl at the run made of what
    was heard.

Paid since K05_port: PtsAre (pts_top), SlotsH (slotsH_at), joinF (hj_top_v), the two ties of the
lookup's inner point, the facts of
the plan on units (place_kr, place_scores, below_fm, sizes_of_hid), LookPts, UnitPtsM, UnitPtsD
(lookAll_of_k3), Numerals at
Reading.gl (gl_numerals).
Premises left. Public: shapeHid's return; PlanLaw; the base parameters' sizes, calls and numbers;
three UnitIs; Fits with the two
block sizes; the join's letters (hscl; hjv: the join's worth at what the lookup heard is its worth
at the letters of Q, for all key values). Of the lookup's kind: K3Pts. Of the hearing: Said; Sized;
the four ties; the
claims; LeftIs. Of the gathering: the returns of pointsOf, the three runs and Look.joinF; the two
points' texts; which record the
runs read. What must be worth 0 or true: AllZero; the join's form; Agree. None of these is shown in
this file or in what it imports.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05PortSlots
import Johnson.Desc.First.Att.K05LookAll
import Johnson.Desc.First.Att.Claims.PortTopV

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

/-- **One fact of the lookup's files for both records**: K3Pts (Att/K05LookAll.lean) gives the
record LookAll of
Att/Claims/LookKeys.lean at every record of challenges whose lookup's end point is z, and KeyIs at
the four calls. -/
theorem k3_look {fs : Model.Forest.Shape} {zx zy : Array E} {zk : Array (Array E)} {z : ℕ → Cb.Gl.E}
    (H : K3Pts fs zx zy zk z) (p : AttSeg.Pub Cb.Gl.E) (hp : p.z = z) :
    K5Law.LookAll Reading.gl fs zx zy p ∧ ∀ q : Fin 4, K5Law.KeyIs fs zx zy (zk.getD q.val #[]) q :=
  ⟨⟨H.nx, H.ny, fun t => by rw [hp, H.z]; rfl⟩, H.zk⟩

variable {K : Type} [Field K] {ρ : Reading K}

/-- pointsOf lays the position's part of the inner point of the unit "wl" as d.ziW. -/
theorem points_ziW {g : Geo} {zk : Array (Array E)} {h : Heard} {l : Left} {p : Pts} (hp : pointsOf g zk h l = some p) :
    ∃ wl, g.single .wl = some wl ∧
      p.d.ziW = (inner wl (zk.getD wl.call #[])).extract (1 + g.lgk) (1 + g.lgk + g.lt) ∧
      (inner wl (zk.getD wl.call #[])).size = 1 + g.lgk + g.lt + g.ldh := by
  unfold pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, K5Law.guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, _, _, _, _, _, uW, hW, _, _, _, _, _, _, _, hz, e⟩ := hp
  subst e
  simp only [Bool.and_eq_true, beq_iff_eq] at hz
  exact ⟨uW, hW, rfl, hz.1.1⟩

/-- **The low part of the position in the inner point of "wl", against yi'**: from LookPts. -/
theorem vi_of {S : Attention.Shape} (gL : Forest.Heard) {i : Runs.In} {zk : Array (Array E)} {h : Heard} {l : Left}
    (hg : i.g = geoOf S) (hP : pointsOf i.g zk h l = some i.p) (N : OnBytes.Road.L5.Norm S) (hl : 1 ≤ S.lnT)
    {C : AttSeg.Calls} {z : ℕ → K}
    (lp : ∀ wl, (geoOf S).single .wl = some wl → LookPts ρ (OnBytes.Road.L5.dimOf S) C z
      (weights wl (zk.getD wl.call #[])) (inner wl (zk.getD wl.call #[]))) :
    ∀ j < S.cf.lB, pt ρ ((oldOf S gL i).d.zilo S) j = yi' (OnBytes.Road.L5.dimOf S) C z j := by
  intro j hj
  obtain ⟨wl, hw, ez, hsz⟩ := points_ziW hP
  rw [hg] at hw ez hsz
  have hlt := N.lt
  have g1 : (geoOf S).lgk = S.cf.lgk := rfl
  have g2 : (geoOf S).lt = S.cf.lt := rfl
  have dlg : (OnBytes.Road.L5.dimOf S).lg = S.cf.lgk := rfl
  have dlP : (OnBytes.Road.L5.dimOf S).lP = S.lnT - 1 := rfl
  have dlT : (OnBytes.Road.L5.dimOf S).lT = S.lnT - 1 + 1 + S.cf.lB := rfl
  have hi := (lp wl hw).hi (S.lnT + j) (by rw [dlT]; omega)
  have sz : i.p.d.ziW.size = S.cf.lt := by
    rw [ez, OnBytes.Road.Rows.sizeCut _ (by rw [hsz]; omega), g1, g2]
    omega
  show pt ρ (i.p.d.ziW.extract S.lnT (S.lnT + S.cf.lB)) j = _
  rw [OnBytes.Road.Rows.ptCut ρ _ (by rw [sz]; omega) (by omega), ez,
    OnBytes.Road.Rows.ptCut ρ _ (by rw [hsz]; omega) (by rw [g1, g2]; omega)]
  unfold pt
  rw [g1, ← dlg, hi]
  show AttSeg.uW _ C z (1 + (OnBytes.Road.L5.dimOf S).lg + (S.lnT + j)) =
    AttSeg.uW _ C z (1 + (OnBytes.Road.L5.dimOf S).lg + ((OnBytes.Road.L5.dimOf S).lP + 1) + j)
  congr 1
  omega

section Top
open Cb.Pv.Att.End (EndLay JoinLay Fits ownCl attA joinF)
open K5Law (PlanLaw AllZero)

variable {M0 Mg X : Type}

/-- **K05_port with its public premises paid.** -/
theorem K05_port_top (P0 : OwnPar Cb.Gl.E M0 X) (Λ : Lin P0 Mg) {G : Fork} {h : Heard} (hk4 : P0.kap = 4) (rows : ℕ)
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
    (h2 : Runs.secondRun i Kc = some l₂) (hZ : AllZero Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry) (l₁ ++ l₂))
    (hptM : (oldOf S gL i).t.ptM = Attention.pointM S (oldOf S gL i).d)
    (hptD : (oldOf S gL i).t.ptD = Attention.pointD S (oldOf S gL i).d)
    {k3 : Runs.PadIn} {kf : Array Aff} (hk : Runs.keysRun i k3 jn = some kf)
    {Fj : Fork} {tj : OnBytes.K.Kc.Tape} {xj : Aff × Fork × OnBytes.K.Kc.Tape}
    (hx : VerifiableInference.Desc.First.Look.joinF gL kf Fj tj = some xj)
    (hv : xj.1.value Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry) = 0)
    {J₂ : Type} [Fintype J₂] [DecidableEq J₂] {Ly : EndLay (closedOf P0 Λ G.ns (numsOf h)) J₂} {Q : JoinLay (closedOf P0 Λ G.ns (numsOf h))} (hFit : Fits Ly Q)
    (hls : Ly.ls = S.ls) (hlm : Ly.lmS = S.cf.lmS) (hscl : (Q.scl.κ 0).sh = S.cf.sh.getD 0 0)
    (hjv : ∀ kv, Cb.Pv.Att.End.joinVal (K5Law.qAt Reading.gl gL) kv (gL.cEnd.value Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry)) =
      Cb.Pv.Att.End.joinVal (Q.q x0) kv ((Q.ce x0).val ((closedOf P0 Λ G.ns (numsOf h)).msg m)))
    (hA : Cb.Sub.Agree (attA Ly (runHeard (closedOf P0 Λ G.ns (numsOf h)) x0 du dt)) ((closedOf P0 Λ G.ns (numsOf h)).msg m) (K5Law.uAt (G.worldOf Reading.gl (Λ.maskOf m) entry) (oldOf S gL i) Kc Ly.Y (OnBytes.Road.Rows.tabOfAtt (oldOf S gL i)) (OnBytes.Road.Rows.placeAtt S))) :
    ∀ f ∈ ownCl Ly Q (runHeard (closedOf P0 Λ G.ns (numsOf h)) x0 du dt),
      (Cb.Sub.pullF (attA Ly (runHeard (closedOf P0 Λ G.ns (numsOf h)) x0 du dt)) f).Holds ((closedOf P0 Λ G.ns (numsOf h)).msg m) := by
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
  have hPts : ∀ a1 a2 k1 k2, i.p.scores[0]? = some k1 → i.p.scores[1]? = some k2 →
      K5Law.PtsAre Reading.gl (oldOf S gL i) (closedOf P0 Λ G.ns (numsOf h)) (runHeard (closedOf P0 Λ G.ns (numsOf h)) x0 du dt) (K5Law.sixTop S i zk a1 a2 k1 k2) :=
    fun a1 a2 k1 k2 e1 e2 => K5Law.pts_top hid PL Lk hK hg hz hP e1 e2 h1 hDS hC
  obtain ⟨a1, a2, k1, k2, ea1, ea2, ek1, ek2, _⟩ := K5Law.six_top (gL := gL) A hid PL hg hz hN hP h1 h2 hZ
  have Sl0 := slotsH_at P0 Λ rows b2 b3 S hDS hnpl nz x0 du dt d1 d2 d3 d4 cu ct m entry gL PA Ap
    (r1 := (0, callOf (OnBytes.Road.L5.callAt S 0), .rm)) (r2 := (0, callOf (OnBytes.Road.L5.callAt S 0), .rd))
    (u1 := ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fm)) (u2 := ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fd)) ea1 ea2 ek1 ek2 (K5Law.uAt (G.worldOf Reading.gl (Λ.maskOf m) entry) (oldOf S gL i) Kc Ly.Y (OnBytes.Road.Rows.tabOfAtt (oldOf S gL i)) (OnBytes.Road.Rows.placeAtt S))
  rw [← K5Law.sixTop_eq hg] at Sl0
  have hj := K5Law.hj_top_v A hid PL Nm Lk hK hg hz hzk hN hP ea1 ea2 ek1 ek2 h1 hk hDS hC hnpl hscl Sl0 hjv hx hv
  have vn := (hPts a1 a2 k1 k2 ek1 ek2).dv.vnW
  have vi := vi_of (ρ := Reading.gl) gL hg hP Nn (Nat.le_of_succ_le Zs.lnT) (C := P0.C) (z := P0.zOf x0)
    (by rw [← hDS]; exact lpW)
  exact K05_port P0 Λ hk4 rows b2 b3 S hDS hlt hNP hgs (K5Law.below_fm _).1 (K5Law.below_fm _).2 nz x0 lpW lpM lpD du dt d1
    d2 d3 d4 cu ct li m entry A gL hg hz hN hP h1 h2 hZ Zs.G hkr Ap hptM hptD vn vi hFit hls hlm
    (fun b1 b2' c1 c2 f1 f2 f3 f4 => ⟨by rw [← K5Law.sixTop_eq hg]; exact hPts b1 b2' c1 c2 f3 f4,
      slotsH_at P0 Λ rows b2 b3 S hDS hnpl nz x0 du dt d1 d2 d3 d4 cu ct m entry gL PA Ap f1 f2 f3 f4 _⟩) hj hA

end Top

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_port_top
#print axioms VerifiableInference.Desc.First.Att.P.vi_of
