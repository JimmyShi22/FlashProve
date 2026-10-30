-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05OutsAre.lean: the record OutsAre of Att/Claims/PortAll.lean (27 fields:
the output statements' points
and challenges are the verifier's; the lengths of what was drawn) at the run made of what was heard
and the
record oldOf S gL i of OnBytes/Model.

Main names:
  `points_tg`: pointsOf lays the first cut of the drawn point as x.tg.
  `ptM_below`, `ptD_on`: the verifier's pointM and pointD, read, are the library's ptBelow and ptOn
    at the sumcheck's
    challenges, read. (Johnson/Road/Rows/AttEnds14Below.lean has the argument inside a longer
      proof.)
  `two_of_map`, `vp_sizes`.
  `outs_are`: all 27 fields, at every parameter record whose sizes are the shape's and with kap = 4.

Premises of outs_are: the shape's Norm; pointsOf's return; the two points' texts; Said; UnitsOfP,
TailOfP; the letters'
claims; the two units' records; two ties of the lookup's inner point (its features' part against yn,
the low part of the
position against yi'); one length.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Outs
import Johnson.Desc.First.Att.Claims.PortMine

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH UnitsClaims seenAfter recOf)
open VerifiableInference.Desc.Part
open Cb.Pv.Att.End (ptN)
open K5Law (oldOf PointsAre points_are chal_are scoreBack Six OutsAre DivIs)
open OnBytes.Road (pt)

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {Mg X : Type}

/-- pointsOf's fields that PointsAre does not name. -/
theorem points_tg {g : Geo} {zk : Array (Array E)} {h : Heard} {l : Left} {p : Pts} (hp : pointsOf g zk h l = some p) :
    p.x.tg = h.point.extract 0 g.lgk := by
  unfold pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, K5Law.guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, e⟩ := hp
  subst e
  rfl

section Points
open OnBytes.Road OnBytes.Road.Rows OnBytes.Attention
open Inst.Model.AttSeg (cat sh yi')
open Cb.Pv.Att.End (ptOn)

omit [Fintype K] in
/-- **The point at which the value product below the diagonal reads the softmax weights**: the
verifier's pointM, read, is the
library's ptBelow at the sumcheck's challenges, read. (Johnson/Road/Rows/AttEnds14Below.lean has
this argument inside a longer
proof.) -/
theorem ptM_below (h : Attention.Heard) (N : L5.Norm h.S) (hl : 1 ≤ h.S.lnT) (C : AttSeg.Calls) (p : AttSeg.Pub K)
    (hr : h.d.vpm.r.size = h.S.cf.lgk + 2 * h.S.lnT - 1 + h.S.cf.lB) (hzi : h.d.ziW.size = h.S.cf.lt)
    (hyi : ∀ j < h.S.cf.lB, pt ρ (h.d.zilo h.S) j = yi' (L5.dimOf h.S) C p.z j) (j : ℕ) (hj : j < h.S.nM) :
    pt ρ (Attention.pointM h.S h.d) j = ptBelow (L5.dimOf h.S) C p (pt ρ h.d.vpm.r) j := by
  have hlt := N.lt
  have dlg : (L5.dimOf h.S).lg = h.S.cf.lgk := rfl
  have dlP : (L5.dimOf h.S).lP = h.S.lnT - 1 := rfl
  have dlB : (L5.dimOf h.S).lB = h.S.cf.lB := rfl
  have q1 : (h.d.vpm.r.extract 0 (h.S.cf.lgk + 2 * h.S.lnT - 1)).size = h.S.cf.lgk + 2 * h.S.lnT - 1 := by
    rw [sizeCut _ (by omega)]
    omega
  have q2 : (h.d.zilo h.S).size = h.S.cf.lB := by
    unfold Attention.Divide.zilo
    rw [sizeCut _ (by omega)]
    omega
  rw [N.nM] at hj
  unfold Attention.pointM ptBelow cat
  show _ = if j < h.S.cf.lgk + (h.S.lnT - 1) + (h.S.lnT - 1 + 1) then _ else
    if j - (h.S.cf.lgk + (h.S.lnT - 1) + (h.S.lnT - 1 + 1)) < h.S.cf.lB then _ else _
  rw [pt_append, Array.size_append, q1, q2, pt_append, q1]
  by_cases a1 : j < h.S.cf.lgk + 2 * h.S.lnT - 1
  · rw [if_pos (by omega), if_pos a1, if_pos (by omega), ptCut ρ _ (by omega) (by omega), Nat.zero_add]
  · by_cases a2 : j < h.S.cf.lgk + 2 * h.S.lnT - 1 + h.S.cf.lB
    · rw [if_pos a2, if_neg a1, if_neg (by omega), if_pos (by omega), hyi _ (by omega)]
      congr 1
      omega
    · rw [if_neg a2, if_neg (by omega), if_neg (by omega)]
      unfold Attention.lastCoords sh
      rw [ptCut ρ _ (Nat.le_refl _) (by omega)]
      congr 1
      omega

omit [Fintype K] in
/-- The same on the diagonal. -/
theorem ptD_on (h : Attention.Heard) (N : L5.Norm h.S) (hl : 1 ≤ h.S.lnT) (C : AttSeg.Calls) (p : AttSeg.Pub K)
    (hr : h.d.vpd.r.size = h.S.cf.lgk + h.S.lnT + h.S.cf.lB) (hzi : h.d.ziW.size = h.S.cf.lt)
    (hyi : ∀ j < h.S.cf.lB, pt ρ (h.d.zilo h.S) j = yi' (L5.dimOf h.S) C p.z j) (j : ℕ) (hj : j < h.S.nD) :
    pt ρ (Attention.pointD h.S h.d) j = ptOn (L5.dimOf h.S) C p (pt ρ h.d.vpd.r) j := by
  have hlt := N.lt
  have dlg : (L5.dimOf h.S).lg = h.S.cf.lgk := rfl
  have dlP : (L5.dimOf h.S).lP = h.S.lnT - 1 := rfl
  have dlB : (L5.dimOf h.S).lB = h.S.cf.lB := rfl
  have q1 : (h.d.vpd.r.extract 0 (h.S.cf.lgk + h.S.lnT)).size = h.S.cf.lgk + h.S.lnT := by
    rw [sizeCut _ (by omega)]
    omega
  have q2 : (h.d.zilo h.S).size = h.S.cf.lB := by
    unfold Attention.Divide.zilo
    rw [sizeCut _ (by omega)]
    omega
  rw [N.nD] at hj
  unfold Attention.pointD ptOn cat
  show _ = if j < h.S.cf.lgk + (h.S.lnT - 1 + 1) then _ else
    if j - (h.S.cf.lgk + (h.S.lnT - 1 + 1)) < h.S.cf.lB then _ else _
  rw [pt_append, Array.size_append, q1, q2, pt_append, q1]
  by_cases a1 : j < h.S.cf.lgk + h.S.lnT
  · rw [if_pos (by omega), if_pos a1, if_pos (by omega), ptCut ρ _ (by omega) (by omega), Nat.zero_add]
  · by_cases a2 : j < h.S.cf.lgk + h.S.lnT + h.S.cf.lB
    · rw [if_pos a2, if_neg a1, if_neg (by omega), if_pos (by omega), hyi _ (by omega)]
      congr 1
      omega
    · rw [if_neg a2, if_neg (by omega), if_neg (by omega)]
      unfold Attention.lastCoords sh
      rw [ptCut ρ _ (Nat.le_refl _) (by omega)]
      congr 1
      omega

end Points

section Outs
open OnBytes.Road
open Inst.Model.AttSeg (yn yi')

theorem two_of_map {α β : Type} {f : α → β} {a : Array α} {x y : β} {k1 k2 : α} (e : a.toList.map f = [x, y])
    (h1 : a[0]? = some k1) (h2 : a[1]? = some k2) : f k1 = x ∧ f k2 = y := by
  rw [← Array.getElem?_toList] at h1 h2
  rcases ha : a.toList with _ | ⟨p, _ | ⟨q, t⟩⟩
  · rw [ha] at e; simp at e
  · rw [ha] at e; simp at e
  · rw [ha] at e h1 h2
    simp only [List.map_cons, List.cons.injEq] at e
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h1 h2
    subst h1 h2
    exact ⟨e.1, e.2.1⟩

/-- The lengths of the two value products' challenges, in the shape's letters. -/
theorem vp_sizes (P : OwnPar K Mg X) {S : Attention.Shape} (gL : Forest.Heard) {i : Runs.In} {zk : Array (Array E)}
    {h : Heard} {l : Left} {G : Fork} {L : Lists} (rows : ℕ) (hD : P.D = L5.dimOf S) (hl : 1 ≤ S.lnT)
    (hP : pointsOf i.g zk h l = some i.p) (b2 : Said (recOf P rows) h G L)
    (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail) (d2 : TailOfP dt (recOf P rows) h L) :
    (oldOf S gL i).d.vpm.r.size = S.cf.lgk + 2 * S.lnT - 1 + S.cf.lB ∧
      (oldOf S gL i).d.vpd.r.size = S.cf.lgk + S.lnT + S.cf.lB := by
  have H := points_are hP
  have elg : P.D.lg = S.cf.lgk := by rw [hD]; rfl
  have elP : P.D.lP = S.lnT - 1 := by rw [hD]; rfl
  have elB : P.D.lB = S.cf.lB := by rw [hD]; rfl
  have nVM : (chal h.below).size = P.D.lg + P.D.lP + (P.D.lP + 1) + P.D.lB := chal_size _ dt.dVM d2.zM d2.oM b2.sM
  have nVD : (chal h.on).size = P.D.lg + (P.D.lP + 1) + P.D.lB := chal_size _ dt.dVD d2.zVD d2.oVD b2.sVD
  constructor
  · show i.p.d.vpm.r.size = _
    rw [H.vpm]
    show (chal h.below).size = _
    omega
  · show i.p.d.vpd.r.size = _
    rw [H.vpd]
    show (chal h.on).size = _
    omega

/-- **OutsAre at the run made of what was heard.** -/
theorem outs_are (P : OwnPar K Mg X) {S : Attention.Shape} (gL : Forest.Heard) {i : Runs.In} {zk : Array (Array E)}
    {h : Heard} {l : Left} {G : Fork} {L : Lists} (rows : ℕ) (hD : P.D = L5.dimOf S) (hk : P.kap = 4)
    (N : L5.Norm S) (hl : 1 ≤ S.lnT) (hg : i.g = geoOf S) (hP : pointsOf i.g zk h l = some i.p)
    (hptM : (oldOf S gL i).t.ptM = Attention.pointM S (oldOf S gL i).d)
    (hptD : (oldOf S gL i).t.ptD = Attention.pointD S (oldOf S gL i).d) (b2 : Said (recOf P rows) h G L) (x0 : X)
    (du : UnitsH ρ (P.own (theMeans K P.D P.C P.kap)).units) (dt : TailH ρ (P.own (theMeans K P.D P.C P.kap)).tail)
    (d1 : UnitsOfP (P.own (theMeans K P.D P.C P.kap)).units du (recOf P rows).score h.scores.toList L.planes.flatten L.units)
    (d2 : TailOfP dt (recOf P rows) h L) (cu : UnitsClaims (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))
    (ct : dt.Claims (seenAfter (P.own (theMeans K P.D P.C P.kap)).units du (x0, []))) {k1 k2 : ScoreP} (hk1 : i.p.scores[0]? = some k1)
    (hk2 : i.p.scores[1]? = some k2) (s : Six) (hsM : s.kM = scoreBack k1) (hsD : s.kD = scoreBack k2)
    (vn : ∀ j < S.cf.ldh, pt ρ (oldOf S gL i).d.zcW j = yn P.D P.C (P.zOf x0) j)
    (vi : ∀ j < S.cf.lB, pt ρ ((oldOf S gL i).d.zilo S) j = yi' (L5.dimOf S) P.C (P.zOf x0) j)
    (hzi : (oldOf S gL i).d.ziW.size = S.cf.lt) :
    OutsAre ρ (oldOf S gL i) P (runHeard P x0 du dt) s := by
  obtain ⟨o1, o2, hos, R⟩ := run_pts P x0 (x := recOf P rows) rfl b2 du dt d1 d2 cu ct
  have H := points_are hP
  have ec := chal_are H
  rw [hos] at ec
  obtain ⟨c1, c2⟩ := two_of_map (f := fun k : ScoreP => k.sc.r) ec hk1 hk2
  have elg : P.D.lg = S.cf.lgk := by rw [hD]; rfl
  have elP : P.D.lP = S.lnT - 1 := by rw [hD]; rfl
  have elB : P.D.lB = S.cf.lB := by rw [hD]; rfl
  have eln : P.D.ln = S.cf.ldh := by rw [hD]; rfl
  have elT : P.D.lT = S.cf.lt := by
    rw [N.lt, ← elP, ← elB]
    rfl
  have rE : (oldOf S gL i).d.scE.r = chal h.division := by
    show i.p.d.scE.r = _
    rw [H.scE]; rfl
  have rVM : (oldOf S gL i).d.vpm.r = chal h.below := by
    show i.p.d.vpm.r = _
    rw [H.vpm]; rfl
  have rVD : (oldOf S gL i).d.vpd.r = chal h.on := by
    show i.p.d.vpd.r = _
    rw [H.vpd]; rfl
  have rF : (oldOf S gL i).x.scF.r = chal h.atIndex := by
    show i.p.x.scF.r = _
    rw [H.scF]; rfl
  have rK : (oldOf S gL i).x.scd.r = chal h.key := by
    show i.p.x.scd.r = _
    rw [H.scd]; rfl
  have rH : (oldOf S gL i).x.scH.r = chal h.cells := by
    show i.p.x.scH.r = _
    rw [H.scH]; rfl
  have rM1 : s.kM.sc.r = chal o1.2 := by rw [hsM]; exact c1
  have rD1 : s.kD.sc.r = chal o2.2 := by rw [hsD]; exact c2
  have nM : (chal o1.2).size = P.D.lg + P.D.lP + (P.D.lP + 1) + P.D.ln := R.nM
  have nD : (chal o2.2).size = P.D.lg + (P.D.lP + 1) + P.D.ln := R.nD
  have nE : (chal h.division).size = P.D.lg + P.D.lT := R.nE
  have nVM : (chal h.below).size = P.D.lg + P.D.lP + (P.D.lP + 1) + P.D.lB := R.nVM
  have nVD : (chal h.on).size = P.D.lg + (P.D.lP + 1) + P.D.lB := R.nVD
  have nF : (chal h.atIndex).size = P.D.lT + P.D.lg + P.D.ln := R.nF
  have nK : (chal h.key).size = P.D.lT + P.D.lg + P.D.lT := R.nK
  have nH : (chal h.cells).size = P.D.lT + P.D.lg + P.kap := R.nH
  have egam : ρ.val (oldOf S gL i).d.gam = ρ.val dt.xV := by
    show ρ.val i.p.d.gam = _
    rw [H.gam, gam_read b2, d2.xV]
  have etg : (oldOf S gL i).x.tg = h.point.extract 0 S.cf.lgk := by
    show i.p.x.tg = _
    rw [points_tg hP, hg]
    rfl
  have npt : h.point.size = 2 * P.D.lg + 2 * P.D.lT + 4 := by
    rw [b2.point, List.size_toArray, b2.lPt]
    rfl
  refine
    { rM := ?_, xM := ?_, rD := ?_, xD := ?_, rE := ?_, xE := ?_, ynE := vn, rVM := ?_, xVM := ?_, ptVM := ?_,
      ynVM := vn, thVM := egam, rVD := ?_, xVD := ?_, ptVD := ?_, ynVD := vn, thVD := egam, th := egam, tg := ?_,
      vtg := ?_, rF := ?_, xF := ?_, rK := ?_, xK := ?_, fn := ?_, rH := ?_, xH := ?_ }
  · rw [rM1, nM, eln]; rfl
  · exact fun j _ => by rw [rM1, R.xM]
  · rw [rD1, nD, eln]; rfl
  · exact fun j _ => by rw [rD1, R.xD]
  · rw [rE, nE, elg]; exact Nat.le_add_right _ _
  · exact fun j _ => by rw [rE, R.xE]
  · rw [rVM, nVM, elg]
    show S.cf.lgk ≤ _
    omega
  · exact fun j _ => by rw [rVM, R.xVM]
  · intro j hj
    have e := ptM_below (ρ := ρ) (oldOf S gL i) N hl P.C (runHeard P x0 du dt).oVM.st
      (by rw [rVM, nVM, elg, elP, elB]; show _ = S.cf.lgk + 2 * S.lnT - 1 + S.cf.lB; omega) hzi vi j
      (Nat.lt_of_lt_of_le hj (Nat.sub_le _ _))
    rw [hptM]
    refine e.trans ?_
    rw [rVM, R.xVM, hD]
    rfl
  · rw [rVD, nVD, elg]
    show S.cf.lgk ≤ _
    omega
  · exact fun j _ => by rw [rVD, R.xVD]
  · intro j hj
    have e := ptD_on (ρ := ρ) (oldOf S gL i) N hl P.C (runHeard P x0 du dt).oVD.st
      (by rw [rVD, nVD, elg, elP, elB]; show _ = S.cf.lgk + S.lnT + S.cf.lB; omega) hzi vi j
      (Nat.lt_of_lt_of_le hj (Nat.sub_le _ _))
    rw [hptD]
    refine e.trans ?_
    rw [rVD, R.xVD, hD]
    rfl
  · rw [etg, Rows.sizeCut _ (by rw [npt, elg]; omega)]
    rfl
  · intro j hj
    have hj' : j < S.cf.lgk := hj
    rw [etg, Rows.ptCut ρ _ (by rw [npt, elg]; omega) (by omega), Nat.zero_add,
      run_tg_read P x0 du dt j (by show j < P.D.lg + P.D.lT; omega), d2.pts, b2.point]
    unfold pt
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]
  · rw [rF, nF, elT, elg, eln]; rfl
  · exact fun j _ => by rw [rF, R.xF]
  · rw [rK, nK, elT, elg]
    show _ = 2 * S.cf.lt + S.cf.lgk
    omega
  · exact fun j _ => by rw [rK, R.xK]
  · intro j hj
    have hj' : j < S.cf.ldh := hj
    rw [run_fn P x0 du dt b2 d2 ct j]
    show pt ρ ((oldOf S gL i).x.scF.r.extract (S.cf.lt + S.cf.lgk) (oldOf S gL i).x.scF.r.size) j = _
    rw [Rows.ptCut ρ _ (Nat.le_refl _) (by rw [rF, nF, elT, elg, eln]; omega), rF, elT, elg]
    rfl
  · rw [rH, nH, elT, elg, hk]; rfl
  · exact fun j _ => by rw [rH, R.xH]

end Outs

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.outs_are
