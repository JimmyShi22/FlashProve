-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05RunIs.lean: the record RunIs of Att/Claims/AgreeTop.lean (28 fields: what
the run made of what was heard gives
for "the tables are true") at that run and the record oldOf S gL i of OnBytes/Model.

Main names:
  `points_ti`: pointsOf lays the second cut of the drawn point as x.ti. `run_ti_read`.
  `OldIs`, `old_is`, `old_sizes`: the record's eight arrays of challenges are the hearing's; their
    lengths in the shape's letters.
  `run_ti_fn`, `run_ptMD`, `run_zM`, `run_zD`: the fields in three lots.
  `run_is`: all 28 fields, at every parameter record whose sizes are the shape's, whose calls are
    callsOf fs, and with kap = 4.

Premises of run_is: the shape's Norm; pointsOf's return; the two points' texts and lengths; Said;
UnitsOfP, TailOfP; the letters'
claims; the two units' records; one tie of the lookup's inner point (the low part of the position
against yi'); one length.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05OutsAre
import Johnson.Desc.First.Att.Claims.AgreeTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH UnitsClaims seenAfter recOf)
open VerifiableInference.Desc.Part
open Cb.Pv.Att.End (ptN)
open K5Law (oldOf PointsAre points_are chal_are scoreBack RunIs xiOf)
open OnBytes.Road
open Inst.Model.AttSeg (yi')

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {Mg X : Type}

theorem points_ti {g : Geo} {zk : Array (Array E)} {h : Heard} {l : Left} {p : Pts} (hp : pointsOf g zk h l = some p) :
    p.x.ti = h.point.extract g.lgk (g.lgk + g.lt) := by
  unfold pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, K5Law.guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, e⟩ := hp
  subst e
  rfl

theorem run_ti_read (P : OwnPar K Mg X) (x0 : X) (du : UnitsH ρ (P.own (theMeans K P.D P.C P.kap)).units) (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail) (j : ℕ)
    (hj : P.D.lg + j < P.g1) :
    (P.pubZ (runHeard P x0 du dt).z).ti j = ρ.val (dt.pts.getD (P.D.lg + j) zeroE) :=
  nat_cut1 P.g1 P.g2 dt.pts (P.D.lg + j) hj

/-- The older record's eight arrays of challenges are the hearing's. -/
structure OldIs (S : Attention.Shape) (gL : Forest.Heard) (i : Runs.In) (h : Heard) (o1 o2 : ℕ × MaskedSum.Heard)
    (k1 k2 : ScoreP) : Prop where
  rM : (scoreBack k1).sc.r = chal o1.2
  rD : (scoreBack k2).sc.r = chal o2.2
  rE : (oldOf S gL i).d.scE.r = chal h.division
  rVM : (oldOf S gL i).d.vpm.r = chal h.below
  rVD : (oldOf S gL i).d.vpd.r = chal h.on
  rF : (oldOf S gL i).x.scF.r = chal h.atIndex
  rK : (oldOf S gL i).x.scd.r = chal h.key
  rH : (oldOf S gL i).x.scH.r = chal h.cells

theorem old_is {S : Attention.Shape} (gL : Forest.Heard) {i : Runs.In} {zk : Array (Array E)} {h : Heard} {l : Left}
    (hP : pointsOf i.g zk h l = some i.p) {o1 o2 : ℕ × MaskedSum.Heard} (hos : h.scores.toList = [o1, o2])
    {k1 k2 : ScoreP} (hk1 : i.p.scores[0]? = some k1) (hk2 : i.p.scores[1]? = some k2) :
    OldIs S gL i h o1 o2 k1 k2 := by
  have H := points_are hP
  have ec := chal_are H
  rw [hos] at ec
  obtain ⟨c1, c2⟩ := two_of_map (f := fun k : ScoreP => k.sc.r) ec hk1 hk2
  refine ⟨c1, c2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show i.p.d.scE.r = _
    rw [H.scE]; rfl
  · show i.p.d.vpm.r = _
    rw [H.vpm]; rfl
  · show i.p.d.vpd.r = _
    rw [H.vpd]; rfl
  · show i.p.x.scF.r = _
    rw [H.scF]; rfl
  · show i.p.x.scd.r = _
    rw [H.scd]; rfl
  · show i.p.x.scH.r = _
    rw [H.scH]; rfl

/-- The eight lengths, in the shape's letters. -/
theorem old_sizes (P : OwnPar K Mg X) {S : Attention.Shape} {gL : Forest.Heard} {i : Runs.In} {h : Heard}
    {o1 o2 : ℕ × MaskedSum.Heard} {k1 k2 : ScoreP} (hD : P.D = L5.dimOf S) (N : L5.Norm S) (hl : 1 ≤ S.lnT) (hk : P.kap = 4) {u : P.Run}
    (O : OldIs S gL i h o1 o2 k1 k2) (R : RunPts (ρ := ρ) P u h o1 o2) :
    (scoreBack k1).sc.r.size = S.cf.lgk + 2 * S.lnT - 1 + S.cf.ldh ∧
    (scoreBack k2).sc.r.size = S.cf.lgk + S.lnT + S.cf.ldh ∧
    (oldOf S gL i).d.scE.r.size = S.cf.lgk + S.cf.lt ∧
    (oldOf S gL i).d.vpm.r.size = S.cf.lgk + 2 * S.lnT - 1 + S.cf.lB ∧
    (oldOf S gL i).d.vpd.r.size = S.cf.lgk + S.lnT + S.cf.lB ∧
    (oldOf S gL i).x.scF.r.size = S.cf.lt + S.cf.lgk + S.cf.ldh ∧
    (oldOf S gL i).x.scd.r.size = 2 * S.cf.lt + S.cf.lgk ∧
    (oldOf S gL i).x.scH.r.size = S.cf.lt + S.cf.lgk + 4 := by
  have elg : P.D.lg = S.cf.lgk := by rw [hD]; rfl
  have elP : P.D.lP = S.lnT - 1 := by rw [hD]; rfl
  have elB : P.D.lB = S.cf.lB := by rw [hD]; rfl
  have eln : P.D.ln = S.cf.ldh := by rw [hD]; rfl
  have elT : P.D.lT = S.cf.lt := by
    rw [N.lt, ← elP, ← elB]
    rfl
  have hlt := N.lt
  have nM : (chal o1.2).size = P.D.lg + P.D.lP + (P.D.lP + 1) + P.D.ln := R.nM
  have nD : (chal o2.2).size = P.D.lg + (P.D.lP + 1) + P.D.ln := R.nD
  have nE : (chal h.division).size = P.D.lg + P.D.lT := R.nE
  have nVM : (chal h.below).size = P.D.lg + P.D.lP + (P.D.lP + 1) + P.D.lB := R.nVM
  have nVD : (chal h.on).size = P.D.lg + (P.D.lP + 1) + P.D.lB := R.nVD
  have nF : (chal h.atIndex).size = P.D.lT + P.D.lg + P.D.ln := R.nF
  have nK : (chal h.key).size = P.D.lT + P.D.lg + P.D.lT := R.nK
  have nH : (chal h.cells).size = P.D.lT + P.D.lg + P.kap := R.nH
  rw [O.rM, O.rD, O.rE, O.rVM, O.rVD, O.rF, O.rK, O.rH, nM, nD, nE, nVM, nVD, nF, nK, nH, hk]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- The second cut of the drawn point, and the feature part of the point of the score at the index.
-/
theorem run_ti_fn (P : OwnPar K Mg X) {S : Attention.Shape} (gL : Forest.Heard) {i : Runs.In} {zk : Array (Array E)}
    {h : Heard} {l : Left} {G : Fork} {L : Lists} (rows : ℕ) (hD : P.D = L5.dimOf S) (N : L5.Norm S) (hg : i.g = geoOf S)
    (hP : pointsOf i.g zk h l = some i.p) (b2 : Said (recOf P rows) h G L) (x0 : X)
    (du : UnitsH ρ (P.own (theMeans K P.D P.C P.kap)).units) (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail) (d2 : TailOfP dt (recOf P rows) h L)
    (ct : dt.Claims (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, [])))
    (rF : (oldOf S gL i).x.scF.r = chal h.atIndex)
    (sF : (oldOf S gL i).x.scF.r.size = S.cf.lt + S.cf.lgk + S.cf.ldh) :
    (oldOf S gL i).x.ti.size = S.cf.lt ∧
    (∀ j < S.cf.lt, pt ρ (oldOf S gL i).x.ti j = (P.pubZ (runHeard P x0 du dt).z).ti j) ∧
    ∀ j < S.cf.ldh, pt ρ ((oldOf S gL i).x.rc S) j = (Prod.fst (runHeard P x0 du dt).oK.st).fn j := by
  have elg : P.D.lg = S.cf.lgk := by rw [hD]; rfl
  have elP : P.D.lP = S.lnT - 1 := by rw [hD]; rfl
  have elB : P.D.lB = S.cf.lB := by rw [hD]; rfl
  have eln : P.D.ln = S.cf.ldh := by rw [hD]; rfl
  have elT : P.D.lT = S.cf.lt := by
    rw [N.lt, ← elP, ← elB]
    rfl
  have hlt := N.lt
  have eti : (oldOf S gL i).x.ti = h.point.extract S.cf.lgk (S.cf.lgk + S.cf.lt) := by
    show i.p.x.ti = _
    rw [points_ti hP, hg]
    rfl
  have npt : h.point.size = 2 * P.D.lg + 2 * P.D.lT + 4 := by
    rw [b2.point, List.size_toArray, b2.lPt]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [eti, Rows.sizeCut _ (by rw [npt, elg, elT]; omega)]
    omega
  · intro j hj
    rw [eti, Rows.ptCut ρ _ (by rw [npt, elg, elT]; omega) (by omega),
      run_ti_read P x0 du dt j (by show P.D.lg + j < P.D.lg + P.D.lT; omega), d2.pts, b2.point, elg]
    unfold pt
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
  · intro j hj
    rw [run_fn P x0 du dt b2 d2 ct j]
    show pt ρ ((oldOf S gL i).x.scF.r.extract (S.cf.lt + S.cf.lgk) (oldOf S gL i).x.scF.r.size) j = _
    rw [Rows.ptCut ρ _ (Nat.le_refl _) (by rw [sF]; omega), rF, elT, elg]
    rfl

/-- The two points at which the value products read the softmax weights, on their whole length. -/
theorem run_ptMD (P : OwnPar K Mg X) {S : Attention.Shape} (gL : Forest.Heard) {i : Runs.In} (C : AttSeg.Calls)
    (N : L5.Norm S) (hl : 1 ≤ S.lnT) (x0 : X) (du : UnitsH ρ (P.own (theMeans K P.D P.C P.kap)).units) (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail)
    (hptM : (oldOf S gL i).t.ptM = Attention.pointM S (oldOf S gL i).d)
    (hptD : (oldOf S gL i).t.ptD = Attention.pointD S (oldOf S gL i).d)
    (sVM : (oldOf S gL i).d.vpm.r.size = S.cf.lgk + 2 * S.lnT - 1 + S.cf.lB)
    (sVD : (oldOf S gL i).d.vpd.r.size = S.cf.lgk + S.lnT + S.cf.lB)
    (xVM : ptN P.sVM.T (runHeard P x0 du dt).oVM = pt ρ (oldOf S gL i).d.vpm.r)
    (xVD : ptN P.sVD.T (runHeard P x0 du dt).oVD = pt ρ (oldOf S gL i).d.vpd.r)
    (vi : ∀ j < S.cf.lB, pt ρ ((oldOf S gL i).d.zilo S) j = yi' (L5.dimOf S) C (P.zOf x0) j)
    (hzi : (oldOf S gL i).d.ziW.size = S.cf.lt) :
    (∀ j < S.nM, pt ρ (oldOf S gL i).t.ptM j =
      ptBelow (L5.dimOf S) C (runHeard P x0 du dt).oVM.st (ptN P.sVM.T (runHeard P x0 du dt).oVM) j) ∧
    ∀ j < S.nD, pt ρ (oldOf S gL i).t.ptD j =
      Cb.Pv.Att.End.ptOn (L5.dimOf S) C (runHeard P x0 du dt).oVD.st (ptN P.sVD.T (runHeard P x0 du dt).oVD) j := by
  have viM : ∀ j < S.cf.lB, pt ρ ((oldOf S gL i).d.zilo S) j =
      yi' (L5.dimOf S) C (AttSeg.Pub.z (runHeard P x0 du dt).oVM.st) j := by
    rw [run_zVM P x0 du dt]; exact vi
  have viD : ∀ j < S.cf.lB, pt ρ ((oldOf S gL i).d.zilo S) j =
      yi' (L5.dimOf S) C (AttSeg.Pub.z (runHeard P x0 du dt).oVD.st) j := by
    rw [run_zVD P x0 du dt]; exact vi
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · rw [hptM, xVM]
    exact ptM_below (ρ := ρ) (oldOf S gL i) N hl C (runHeard P x0 du dt).oVM.st sVM hzi viM j hj
  · rw [hptD, xVD]
    exact ptD_on (ρ := ρ) (oldOf S gL i) N hl C (runHeard P x0 du dt).oVD.st sVD hzi viD j hj

theorem run_zM (P : OwnPar K Mg X) (x0 : X) (du : UnitsH ρ (P.own (theMeans K P.D P.C P.kap)).units) (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail) :
    AttSeg.Pub.z (runHeard P x0 du dt).oM.st = P.zOf x0 := rfl
theorem run_zD (P : OwnPar K Mg X) (x0 : X) (du : UnitsH ρ (P.own (theMeans K P.D P.C P.kap)).units) (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail) :
    AttSeg.Pub.z (runHeard P x0 du dt).oD.st = P.zOf x0 := rfl

/-- **RunIs at the run made of what was heard.** -/
theorem run_is (P : OwnPar K Mg X) {S : Attention.Shape} {fs : Model.Forest.Shape} (gL : Forest.Heard) {i : Runs.In}
    {zk : Array (Array E)} {h : Heard} {l : Left} {G : Fork} {L : Lists} (rows : ℕ) (hD : P.D = L5.dimOf S)
    (hC : P.C = L5.callsOf fs) (hk : P.kap = 4) (N : L5.Norm S) (hl : 1 ≤ S.lnT) (hg : i.g = geoOf S)
    (hP : pointsOf i.g zk h l = some i.p)
    (hptM : (oldOf S gL i).t.ptM = Attention.pointM S (oldOf S gL i).d)
    (hptD : (oldOf S gL i).t.ptD = Attention.pointD S (oldOf S gL i).d)
    (sPM : (oldOf S gL i).t.ptM.size = S.nM) (sPD : (oldOf S gL i).t.ptD.size = S.nD)
    (b2 : Said (recOf P rows) h G L) (x0 : X)
    (du : UnitsH ρ (P.own (theMeans K P.D P.C P.kap)).units) (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail)
    (d1 : UnitsOfP (P.own (theMeans K P.D P.C P.kap)).units du (recOf P rows).score h.scores.toList L.planes.flatten L.units)
    (d2 : TailOfP dt (recOf P rows) h L) (cu : UnitsClaims (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))
    (ct : dt.Claims (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))) {k1 k2 : ScoreP} (hk1 : i.p.scores[0]? = some k1)
    (hk2 : i.p.scores[1]? = some k2)
    (vi : ∀ j < S.cf.lB, pt ρ ((oldOf S gL i).d.zilo S) j = yi' (L5.dimOf S) P.C (P.zOf x0) j)
    (hzi : (oldOf S gL i).d.ziW.size = S.cf.lt) :
    RunIs ρ (oldOf S gL i) (scoreBack k1) (scoreBack k2) (L5.callsOf fs) (xiOf (runHeard P x0 du dt)) := by
  obtain ⟨o1, o2, hos, R⟩ := run_pts P x0 (x := recOf P rows) rfl b2 du dt d1 d2 cu ct
  have O := old_is (S := S) gL hP hos hk1 hk2
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩ := old_sizes P hD N hl hk O R
  obtain ⟨t1, t2, t3⟩ := run_ti_fn P gL rows hD N hg hP b2 x0 du dt d2 ct O.rF s6
  rw [hC] at vi
  obtain ⟨p1, p2⟩ := run_ptMD P gL (L5.callsOf fs) N hl x0 du dt hptM hptD s4 s5 (by rw [O.rVM]; exact R.xVM)
    (by rw [O.rVD]; exact R.xVD) vi hzi
  exact
    { zM := run_zM P x0 du dt, zD := run_zD P x0 du dt, zE := run_zE P x0 du dt, zVM := run_zVM P x0 du dt,
      zVD := run_zVD P x0 du dt, rM := s1, pM := fun j => by rw [O.rM]; exact congrFun R.xM j, rD := s2,
      pD := fun j => by rw [O.rD]; exact congrFun R.xD j, rE := s3, pE := fun j => by rw [O.rE]; exact congrFun R.xE j,
      rVM := s4, pVM := fun j => by rw [O.rVM]; exact congrFun R.xVM j, rVD := s5,
      pVD := fun j => by rw [O.rVD]; exact congrFun R.xVD j, rF := s6, pF := fun j => by rw [O.rF]; exact congrFun R.xF j,
      rK := s7, pK := fun j => by rw [O.rK]; exact congrFun R.xK j, rH := by rw [s8]; exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _),
      pH := fun j => by rw [O.rH]; exact congrFun R.xH j, sti := t1, ti := t2, fn := t3, sPM := sPM, ptM := p1, sPD := sPD,
      ptD := p2 }

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.run_is
