-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Agree.lean: the library's form Agree in GatheredTop (Att/K05RowTop.lean),
drawn from the verifier's form AttAt and
from CellsTie, by agree_top (Att/Claims/AgreeTop.lean) and run_is (Att/K05RunIs.lean). That the
tables are true is not shown: it stays
a premise, in the form in which the smallness test's kind can give it.

Main names:
  `GatheredAll`: GatheredTop with, in the place of Agree and of the two points' texts: tablesP's
    return; "the tables were made at the
    lookup's own point"; AttAt (every table of the list is true of the matrices M in the world; the
      matrices fit; the planner's
    shape; numerals); CellsTie (the early entry of each cell is the matrices' entry at the cell's
      address).
  `gatheredTop_of_all`: GatheredAll gives GatheredTop.

Premises of gatheredTop_of_all: kap = 4; shapeHid's return; PlanLaw; the base parameters' sizes and
calls; three UnitIs; the two block
sizes are the shape's; every late entry's name is listed; K3Pts; Said.
No conjunct of GatheredAll is shown in this file or in what it imports.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05RowTop
import Johnson.Desc.First.Att.K05RunIs

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

/-- **What stands behind the kind, with Agree drawn from AttAt and CellsTie: that the tables are
true stays a premise, in the form
in which the smallness test's kind can give it.** -/
def GatheredAll (P0 : OwnPar Cb.Gl.E M0 X) (Λ : Lin P0 Mg) (ns : ℕ) (N : Nums) (rows : ℕ) (S : Attention.Shape)
    (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape)
    {J₂ : Type} [Fintype J₂] [DecidableEq J₂] (Ly : EndLay (closedOf P0 Λ ns N) J₂) (Q : JoinLay (closedOf P0 Λ ns N)) (zx : Array E)
    (zk : Array (Array E)) (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (G : Fork) (h : Heard) (L : Lists) (x0 : X) (m : Mg) : Prop :=
  ∀ (nz : BetasNz Reading.gl L) (du : UnitsH Reading.gl ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units) (dt : TailH Reading.gl ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).tail),
    UnitsOfP ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units du (recOf (closedOf P0 Λ ns N) rows).score h.scores.toList L.planes.flatten L.units →
    TailOfP dt (recOf (closedOf P0 Λ ns N) rows) h L →
    UnitsVals ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units du
      (unitsAdd (ρ := Reading.gl) ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units (landedUnits _ _) L.planes.flatten L.units (x0, [])) →
    TailVals dt (tailAdd ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).tail L h nz (landedTail _ _) (seenAfter ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units du (x0, []))) →
    ∃ (l : Left) (A : Attention.Plan) (gL : Forest.Heard) (i : Runs.In) (Kc : ℕ) (l₁ l₂ : List Aff) (jn : Runs.JoinsP)
      (k3 : Runs.PadIn) (kf : Array Aff) (Fj : Fork) (tj : OnBytes.K.Kc.Tape) (xj : Aff × Fork × OnBytes.K.Kc.Tape)
      (tl : HTailF2) (nW : ℕ) (lk : LookIn) (M : OnBytes.Road.Mats Cb.Gl.E),
      LeftIs (geoOf S) zk h G l ∧ i.g = geoOf S ∧ i.zk = gL.zk ∧ gL.zk = zk ∧ A.NC = S.calls.size ∧
      pointsOf i.g zk h l = some i.p ∧ Runs.firstRun i Kc = some (l₁, jn) ∧ Runs.secondRun i Kc = some l₂ ∧
      AllZero Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry) (l₁ ++ l₂) ∧
      Runs.keysRun i k3 jn = some kf ∧ VerifiableInference.Desc.First.Look.joinF gL kf Fj tj = some xj ∧
      xj.1.value Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry) = 0 ∧
      (∀ kv, Cb.Pv.Att.End.joinVal (K5Law.qAt Reading.gl gL) kv (gL.cEnd.value Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry)) =
        Cb.Pv.Att.End.joinVal (Q.q x0) kv ((Q.ce x0).val ((closedOf P0 Λ ns N).msg m))) ∧
      tablesP i.g (K5Law.matsOf tl.mats) nW lk i.p = some i.t ∧ lk.zx = zx ∧
      OnBytes.Road.Rows.AttAt Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry) tl Kc M (oldOf S gL i) lid cf fs ∧
      K5Law.CellsTie (oldOf S gL i) M Ly.cellJ ((closedOf P0 Λ ns N).msg m)

theorem gatheredTop_of_all (P0 : OwnPar Cb.Gl.E M0 X) (Λ : Lin P0 Mg) (ns : ℕ) (N : Nums) (hk4 : P0.kap = 4) (rows : ℕ)
    {S : Attention.Shape} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}
    (hid : Attention.shapeHid lid cf = Except.ok (S, fs)) (PL : PlanLaw cf S fs)
    (hDS : P0.D = OnBytes.Road.L5.dimOf S) (hC : P0.C = OnBytes.Road.L5.callsOf fs) {qW qM qD : Fin 4}
    (UW : ∀ wl, (geoOf S).single .wl = some wl → UnitIs P0.D P0.C .w3 qW wl)
    (UM : UnitIs P0.D P0.C .m1 qM ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fm)) (UD : UnitIs P0.D P0.C .d1 qD ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fd))
    {J₂ : Type} [Fintype J₂] [DecidableEq J₂] {Ly : EndLay (closedOf P0 Λ ns N) J₂} {Q : JoinLay (closedOf P0 Λ ns N)}
    (hls : Ly.ls = S.ls) (hlm : Ly.lmS = S.cf.lmS)
    (hY : ∀ j, (Ly.Y.nm j).2 ∈ namesOf (OnBytes.Road.L5.dimOf S) S.ls S.cf.lmS (Ly.Y.nm j).1)
    {zx zy : Array E} {zk : Array (Array E)} {entry : ℕ → ℕ → ℕ → Cb.Gl.E} {G : Fork} {h : Heard} {L : Lists} {x0 : X}
    {m : Mg} (H3 : K3Pts fs zx zy zk (P0.zOf x0)) (b2 : Said (recOf (closedOf P0 Λ ns N) rows) h G L)
    (hga : GatheredAll P0 Λ ns N rows S lid cf fs Ly Q zx zk entry G h L x0 m) :
    GatheredTop P0 Λ ns N rows S Ly Q zk entry G h L x0 m := by
  intro nz du dt d1 d2 d3 d4
  obtain ⟨l, A, gL, i, Kc, l₁, l₂, jn, k3, kf, Fj, tj, xj, tl, nW, lk, M, li, hg, hz, hzk, hN, hP, h1, h2, hZ, hk, hx, hv, hjv,
    ht, hzx, At, Ct⟩ := hga nz du dt d1 d2 d3 d4
  subst hzx
  obtain ⟨cu, ct⟩ := claims_of_ties (closedOf P0 Λ ns N) hk4 rows b2 nz x0 du dt d1 d2 d3 d4
  have Nn := OnBytes.Road.Rows.norm_of_hid hid
  have Zs := OnBytes.Road.Rows.sizes_of_hid hid
  have hp : K5Law.PosG i.g := by rw [hg]; exact PL.pos
  have Tb := K5Law.tabs_at (gL := gL) hg ht hp
  have hzi := (K5Law.pub_a (gL := gL) hg (K5Law.points_more hP)).zi
  obtain ⟨lpW, _, _⟩ := lookAll_of_k3 P0 S PL.fit hC zk ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fm) ((geoOf S).unitAt 1 (callOf (OnBytes.Road.L5.callAt S 1)) .fd) x0 H3 UW UM UD
  obtain ⟨Lk, hK⟩ := k3_look H3 ((closedOf P0 Λ ns N).pub0 (runHeard (closedOf P0 Λ ns N) x0 du dt).y0) rfl
  obtain ⟨a1, a2, k1, k2, _, _, ek1, ek2, _⟩ := K5Law.six_top (gL := gL) A hid PL hg hz hN hP h1 h2 hZ
  have vi := vi_of (ρ := Reading.gl) gL hg hP Nn (Nat.le_of_succ_le Zs.lnT) (C := P0.C) (z := P0.zOf x0)
    (by rw [← hDS]; exact lpW)
  have Zz : K5Law.SizesAre (closedOf P0 Λ ns N) Ly (oldOf S gL i) := ⟨hDS, hk4, hls, hlm⟩
  obtain ⟨sVM, sVD⟩ := vp_sizes (closedOf P0 Λ ns N) gL rows hDS (Nat.le_of_succ_le Zs.lnT) hP b2 dt d2
  have Sn := K5Law.shape_nums Zz At.pub Tb.ptM Tb.ptD sVM sVD hzi
  have R := run_is (closedOf P0 Λ ns N) (fs := fs) gL rows hDS hC hk4 Nn (Nat.le_of_succ_le Zs.lnT) hg hP Tb.ptM Tb.ptD Sn.ptM Sn.ptD b2 x0
    du dt d1 d2 cu ct ek1 ek2 vi hzi
  exact ⟨l, A, gL, i, Kc, l₁, l₂, jn, k3, kf, Fj, tj, xj, li, hg, hz, hzk, hN, hP, h1, h2, hZ, Tb.ptM, Tb.ptD, hk, hx, hv, hjv,
    K5Law.agree_top PL Lk hK hg hP ht ek1 ek2 Zz hC At R Ct hY⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.gatheredTop_of_all
