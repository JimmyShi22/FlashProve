-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05GatheredZero.lean: what stands behind the kind (GatheredAllJ,
Att/K05GatheredJ.lean) is met, in the world whose tables are all 0, at
a message whose cells are all 0, wherever the pull-backs of the library's ledger hold and the
gathering returns.

Main names:
  `attAt_zero`: AttAt (Johnson/Road/Rows/AttRead.lean) at the matrices 0 in a world whose entries
    are 0: every table is true there.
  `cellsTie_zero`: CellsTie (Claims/AgreeAll.lean) at the matrices 0 and a message whose cells are
    0.
  `Returns`: the gathering's returns at what was heard and a ledger, and MatsFit. No worth of a form
    is in it.
  `gathered_zero`: GatheredAllJ at the entries 0.

Paid here of GatheredAllJ: every gathered form is worth 0 and the join's form is worth 0
(K05_port_top_back, Att/K05Back.lean); AttAt; CellsTie.
Premises left: Returns; the join's tie Jn and hjv at the record gL of Returns, in this one world;
the message's cells are 0; typed data with the four ties at which the
pull-backs hold; the public premises of K05_port_top.
Limits. The cells are 0 and the tables are 0, on purpose; the mask entries are free. No view is
shown here at which Returns holds: that is
Att/K05ReturnsAt.lean.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Back
import Johnson.Desc.First.Att.K05GatheredJ
import Johnson.Desc.First.Att.K05One

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole IOR OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH UnitsClaims seenAfter recOf)
open VerifiableInference.Desc.Part
open K5Law (oldOf PlanLaw AllZero)
open Cb.Pv.Att.End (EndLay JoinLay Fits ownCl attA namesOf)

variable {M0 Mg X : Type}

/-- Every table is true of the matrices 0 in a world whose entries are 0. -/
theorem attAt_zero {W : World Cb.Gl.E} (hW : ∀ a r c, W.entry a r c = 0) {tl : HTailF2} (Kc : ℕ) {hh : Attention.Heard}
    {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape} (hid : Attention.shapeHid lid cf = Except.ok (hh.S, fs))
    (hm : OnBytes.Road.Rows.MatsFit hh.S tl) :
    OnBytes.Road.Rows.AttAt Reading.gl W tl Kc (fun _ _ _ => 0) hh lid cf fs :=
  ⟨OnBytes.Road.gl_numerals, hid, hm, fun Fn _ c sg pos _ => by
    rw [hW]
    exact (Finset.sum_eq_zero fun j _ => mul_zero _).symm⟩

/-- The cells' tie at the matrices 0. -/
theorem cellsTie_zero {J₁ : Type} (hh : Attention.Heard) (cellJ : AttSeg.Raw → J₁) (x : J₁ → Cb.Gl.E)
    (h0 : ∀ c, x (cellJ c) = 0) : K5Law.CellsTie hh (fun _ _ _ => 0) cellJ x :=
  ⟨fun _ _ _ _ _ _ => h0 _, fun _ _ _ _ _ _ _ _ => h0 _, fun _ _ _ _ _ _ => h0 _⟩

/-- **The gathering's returns** at what was heard and a ledger; the list of matrices fits. No worth
of a form is in it. -/
structure Returns (S : Attention.Shape) (zx : Array E) (zk : Array (Array E)) (G : Fork) (h : Heard) (l : Left)
    (A : Attention.Plan) (gL : Forest.Heard) (i : Runs.In) (Kc : ℕ) (l₁ l₂ : List Aff) (jn : Runs.JoinsP) (k3 : Runs.PadIn)
    (kf : Array Aff) (Fj : Fork) (tj : OnBytes.K.Kc.Tape) (xj : Aff × Fork × OnBytes.K.Kc.Tape) (tl : HTailF2) (nW : ℕ)
    (lk : LookIn) : Prop where
  left : LeftIs (geoOf S) zk h G l
  geo : i.g = geoOf S
  zkI : i.zk = gL.zk
  zkL : gL.zk = zk
  nc : A.NC = S.calls.size
  points : pointsOf i.g zk h l = some i.p
  first : Runs.firstRun i Kc = some (l₁, jn)
  second : Runs.secondRun i Kc = some l₂
  keys : Runs.keysRun i k3 jn = some kf
  join : VerifiableInference.Desc.First.Look.joinF gL kf Fj tj = some xj
  tables : tablesP i.g (K5Law.matsOf tl.mats) nW lk i.p = some i.t
  zx : lk.zx = zx
  mats : OnBytes.Road.Rows.MatsFit S tl
  /-- the runs write the plan's own number of the tables' array into their forms' entries -/
  u3 : i.iU3 = A.iU3

/-- **What stands behind the kind is met, in the world of tables 0, at a message of cells 0**, where
the pull-backs of the
library's ledger hold at typed data with the four ties and the gathering returns. -/
theorem gathered_zero (P0 : OwnPar Cb.Gl.E M0 X) (Λ : Lin P0 Mg) {G : Fork} {h : Heard} (ns : ℕ) (N : Nums)
    (hns : G.ns = ns) (hNn : numsOf h = N) (hk4 : P0.kap = 4) (rows : ℕ) {S : Attention.Shape} {lid : ℕ}
    {cf : Attention.Cfg} {fs : Model.Forest.Shape} (hid : Attention.shapeHid lid cf = Except.ok (S, fs))
    (PL : PlanLaw cf S fs) (hDS : P0.D = OnBytes.Road.L5.dimOf S)
    (hC : P0.C = OnBytes.Road.L5.callsOf fs) (hnpl : P0.npl = 2) (hlt : S.cf.lt = P0.D.lT)
    (hNP : (geoOf S).NP = (size18 P0.D).pairs) {qW qM qD : Fin 4}
    (UW : ∀ wl, (geoOf S).single .wl = some wl → UnitIs P0.D P0.C .w3 qW wl)
    (UM : UnitIs P0.D P0.C .m1 qM ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fm)) (UD : UnitIs P0.D P0.C .d1 qD ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fd))
    {L : Lists} (b2 : Said (recOf (closedOf P0 Λ ns N) rows) h G L) (b3 : Sized G) {zx zy : Array E} {zk : Array (Array E)} (x0 : X)
    (H3 : K3Pts fs zx zy zk (P0.zOf x0)) (m : Mg)
    {J₂ : Type} [Fintype J₂] [DecidableEq J₂] {Ly : EndLay (closedOf P0 Λ ns N) J₂} {Q : JoinLay (closedOf P0 Λ ns N)} (hFit : Fits Ly Q)
    (hls : Ly.ls = S.ls) (hlm : Ly.lmS = S.cf.lmS) (hscl : (Q.scl.κ 0).sh = S.cf.sh.getD 0 0)
    (hY : ∀ j, (Ly.Y.nm j).2 ∈ namesOf (OnBytes.Road.L5.dimOf S) S.ls S.cf.lmS (Ly.Y.nm j).1)
    (Jn : X → Forest.Heard → World Cb.Gl.E → Mg → Prop)
    (hm0 : ∀ c, (closedOf P0 Λ ns N).msg m (Ly.cellJ c) = 0)
    (nz : BetasNz Reading.gl L) (du : UnitsH Reading.gl ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units) (dt : TailH Reading.gl ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).tail)
    (d1 : UnitsOfP ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units du (recOf (closedOf P0 Λ ns N) rows).score h.scores.toList L.planes.flatten L.units)
    (d2 : TailOfP dt (recOf (closedOf P0 Λ ns N) rows) h L)
    (d3 : UnitsVals ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units du
      (unitsAdd (ρ := Reading.gl) ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units (landedUnits _ _) L.planes.flatten L.units (x0, [])))
    (d4 : TailVals dt (tailAdd ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).tail L h nz (landedTail _ _) (seenAfter ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units du (x0, []))))
    (Hcl : ∀ f ∈ ownCl Ly Q (runHeard (closedOf P0 Λ ns N) x0 du dt),
      (Cb.Sub.pullF (attA Ly (runHeard (closedOf P0 Λ ns N) x0 du dt)) f).Holds ((closedOf P0 Λ ns N).msg m))
    {l : Left} {A : Attention.Plan} {gL : Forest.Heard} {i : Runs.In} {Kc : ℕ} {l₁ l₂ : List Aff} {jn : Runs.JoinsP}
    {k3 : Runs.PadIn} {kf : Array Aff} {Fj : Fork} {tj : OnBytes.K.Kc.Tape} {xj : Aff × Fork × OnBytes.K.Kc.Tape}
    {tl : HTailF2} {nW : ℕ} {lk : LookIn} (Rt : Returns S zx zk G h l A gL i Kc l₁ l₂ jn k3 kf Fj tj xj tl nW lk)
    (hJ : Jn x0 gL (G.worldOf Reading.gl (Λ.maskOf m) fun _ _ _ => 0) m)
    (hjv : ∀ kv, Cb.Pv.Att.End.joinVal (K5Law.qAt Reading.gl gL) kv
        (gL.cEnd.value Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) fun _ _ _ => 0)) =
      Cb.Pv.Att.End.joinVal (Q.q x0) kv ((Q.ce x0).val ((closedOf P0 Λ ns N).msg m))) :
    GatheredAllJ P0 Λ ns N rows S lid cf fs Ly Jn zx zk (fun _ _ _ => 0) G h L x0 m := by
  intro nz' du' dt' e1 e2 e3 e4
  obtain rfl : du = du' := unitsH_one _ _ _ _ _ _ _ _ d1 e1 d3 e3
  obtain rfl : dt = dt' := tailH_one d2 e2 d4 e4
  obtain ⟨li, hg, hz, hzk, hN, hP, h1, h2, hk, hx, ht, hzx, hmf⟩ := Rt
  subst hzx
  subst hns hNn
  obtain ⟨cu, ct⟩ := claims_of_ties (closedOf P0 Λ G.ns (numsOf h)) hk4 rows b2 nz x0 du dt d1 d2 d3 d4
  have Nn := OnBytes.Road.Rows.norm_of_hid hid
  have Zs := OnBytes.Road.Rows.sizes_of_hid hid
  have hp : K5Law.PosG i.g := by rw [hg]; exact PL.pos
  have Tb := K5Law.tabs_at (gL := gL) hg ht hp
  have hzi := (K5Law.pub_a (gL := gL) hg (K5Law.points_more hP)).zi
  obtain ⟨lpW, _, _⟩ := lookAll_of_k3 P0 S PL.fit hC zk ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fm) ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fd) x0 H3 UW UM UD
  obtain ⟨Lk, hK⟩ := k3_look H3 ((closedOf P0 Λ G.ns (numsOf h)).pub0 (runHeard (closedOf P0 Λ G.ns (numsOf h)) x0 du dt).y0) rfl
  have hkr : i.g.units .kr [.rm, .rd] = [(0, callOf (OnBytes.Road.L5.callAt S 0), .rm),
      (0, callOf (OnBytes.Road.L5.callAt S 0), .rd)] := by rw [hg]; exact K5Law.place_kr PL.place
  have hgs' : i.g.scores = [((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fm), ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fd)] := by rw [hg]; exact K5Law.place_scores PL.place
  obtain ⟨a1, a2, k1, k2, _, _, ek1, ek2, _⟩ := K5Law.sayAt_back (ρ := Reading.gl)
    (W := (G.worldOf Reading.gl (Λ.maskOf m) fun _ _ _ => 0)) (gL := gL) A hg hz hN hP h1 h2 Zs.G hkr hgs'
  have vi := vi_of (ρ := Reading.gl) gL hg hP Nn (Nat.le_of_succ_le Zs.lnT) (C := P0.C) (z := P0.zOf x0)
    (by rw [← hDS]; exact lpW)
  have Zz : K5Law.SizesAre (closedOf P0 Λ G.ns (numsOf h)) Ly (oldOf S gL i) := ⟨hDS, hk4, hls, hlm⟩
  obtain ⟨sVM, sVD⟩ := vp_sizes (closedOf P0 Λ G.ns (numsOf h)) gL rows hDS (Nat.le_of_succ_le Zs.lnT) hP b2 dt d2
  have At : OnBytes.Road.Rows.AttAt Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) fun _ _ _ => 0) tl Kc (fun _ _ _ => 0) (oldOf S gL i) lid cf fs :=
    attAt_zero (fun _ _ _ => rfl) Kc hid hmf
  have Ct := cellsTie_zero (oldOf S gL i) Ly.cellJ _ hm0
  have Sn := K5Law.shape_nums Zz At.pub Tb.ptM Tb.ptD sVM sVD hzi
  have R := run_is (closedOf P0 Λ G.ns (numsOf h)) (fs := fs) gL rows hDS hC hk4 Nn (Nat.le_of_succ_le Zs.lnT) hg hP Tb.ptM Tb.ptD Sn.ptM
    Sn.ptD b2 x0 du dt d1 d2 cu ct ek1 ek2 vi hzi
  have hA := K5Law.agree_top PL Lk hK hg hP ht ek1 ek2 Zz hC At R Ct hY
  obtain ⟨hZ, hv⟩ := K05_port_top_back P0 Λ hk4 rows b2 b3 hid PL hDS hC hnpl hlt hNP x0 H3 UW UM UD nz du dt d1 d2 d3 d4 cu
    ct li m (fun _ _ _ => 0) A gL hg hz hzk hN hP h1 h2 Tb.ptM Tb.ptD hk hx hFit hls hlm hscl hjv hA Hcl
  exact ⟨l, A, gL, i, Kc, l₁, l₂, jn, k3, kf, Fj, tj, xj, tl, nW, lk, fun _ _ _ => 0, li, hg, hz, hzk, hN, hP, h1, h2, hZ, hk,
    hx, hv, hJ, ht, rfl, At, Ct⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.gathered_zero
