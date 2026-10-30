-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PortAll.lean: kind K5: the library's ledger of the own rounds' claims
(Cb/Pv/Att/End/Cl.lean: ownCl L Q u) holds where the forms that the kind's claims gather are worth
0: the thirteen parts of Johnson/Desc/First/Att/Claims/PortParts.lean put together, at any
parameters P, letters L and Q, run u and message m, at the late entries read off the world (uAt,
Johnson/Desc/First/Att/Claims/PortDict.lean), with tabOfAtt h (Johnson/Road/Rows/AttPlaces.lean) for
where the tables begin.

Main names:
  `rowF_holds`: the claim on a sumcheck's row reads no late entry: it holds at (x, ul) if and only
    if the block's first output claim UHolds holds at x.
  `port_cl`: ∀ f ∈ ownCl L Q u, f.Holds (Sum.elim (P.msg m) (uAt …)). No table is taken to be true.
  `port_pull`: under Cb.Sub.Agree (attA L u) (P.msg m) (uAt …): ∀ f ∈ ownCl L Q u, (pullF (attA L u)
    f).Holds (P.msg m): the premise of att_last (Cb/Pv/Att/End/Cl.lean).
Premises, in records; none of them but Say, InTail and parts of SixSay and PtsAre is shown in this
file or in what it imports:
  `SizesAre P L h`; AttPub; the library's Fits L Q.
  `ShapeNums P h`: eight numbers of the shape.
  Say ρ W h K3: what the claims say: by say_iff (Johnson/Desc/First/Att/Claims/Say58.lean) it is
    "every gathered form is worth 0". InTail h: in_tail
    (Johnson/Desc/First/Att/Claims/InRunAll.lean).
  `Six`, `SixSay`: what the claims say of the two plane claims and the two units; InUnit (in_unit);
    six small facts on the records.
  `PtsAre`: the verifier's points and weights at the lookup's end point are the library's. Its field
    dv.fe: in_high_fe (Johnson/Desc/First/Att/Claims/InHigh.lean).
  `OutsAre`: the output statements' points and challenges are the verifier's; the lengths of what
    was drawn.
  `SlotsH`: the hidden value under each slot is what was sent or shown less its mask entry, in the
    numbers of h.
  `RowsHold`: the eight sumchecks' claims on their rows.
  hj: the join's claim joinF.
Limit: Agree says that each late entry read off the world is worth its meant form: that the tables
are true: it is what the smallness test is meant to give.
Used: as Johnson/Desc/First/Att/Claims/PortParts.lean and
Johnson/Desc/First/Att/Claims/PortDict.lean; the library's rowF_pull, Fits.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.PortDict
import Johnson.Desc.First.Att.Claims.InHigh
import Johnson.Desc.First.Att.Claims.EndsRun
import Johnson.Desc.First.Att.Claims.PointsMore

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset Cb
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Inst.Model.AttSeg (Raw Calls Pub Step yn Dim zg zgD)
open Cb.Pv.Att (OwnPar ptBelow size18)
open Cb.Pv.Att.End (LateLay AttTab EndLay JoinLay Fits ptN rowF ptOn ownCl joinF attA zT)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (geoOf)
open VerifiableInference.Desc.First.Att.P.Runs (JoinsP)

variable {Kf : Type} [Field Kf] [Fintype Kf] {M X : Type} {J₂ : Type} [Fintype J₂] [DecidableEq J₂]

omit [DecidableEq J₂] in
/-- The claim on a sumcheck's row reads no late entry. -/
theorem rowF_holds {T : Cb.Pv.Att.PlainSc Kf} [DecidableEq T.J] (o : T.our.par.Out) (x : T.J → Kf)
    (ul : J₂ → Kf) : (rowF (J₂ := J₂) T o).Holds (Sum.elim x ul) ↔ T.our.par.UHolds o x := by
  have e := Cb.Sub.pullF_holds (fun j => (⟨fun _ => 0, ul j⟩ : TWhole.Aff Kf T.J)) (rowF T o) x
  have v : (fun i => ((⟨fun _ => 0, ul i⟩ : TWhole.Aff Kf T.J)).val x) = ul := by
    funext i
    simp [TWhole.Aff.val]
  rw [v] at e
  rw [← e]
  exact Cb.Pv.Att.End.rowF_pull T _ o x

variable {ρ : Reading Kf} {W : World Kf} {K3 : ℕ} {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape}
  {P : OwnPar Kf M X} {L : EndLay P J₂} {Q : JoinLay P} {u : P.Run} {m : M}

/-- The segment's two remainder-table plane claims, its two softmax-table units, their plane claims and tables. -/
structure Six where
  pM : PlaneClaim
  pD : PlaneClaim
  kM : Score
  kD : Score
  cM : PlaneClaim
  cD : PlaneClaim

/-- Numbers of the shape that the ports ask for. -/
structure ShapeNums (P : OwnPar Kf M X) (h : Attention.Heard) : Prop where
  q2 : h.S.atQ.nl = 2
  k2 : h.S.atK.nl = 2
  v2 : h.S.atV.nl = 2
  o2 : h.S.atO.nl = 2
  nM : P.D.lM = h.S.nM
  nD : P.D.lD = h.S.nD
  ptM : h.t.ptM.size = h.S.nM
  ptD : h.t.ptD.size = h.S.nD

/-- What the claims say of the six, and small facts on their records. -/
structure SixSay (ρ : Reading Kf) (W : World Kf) (h : Attention.Heard) (K3 : ℕ) (s : Six) : Prop where
  sM : PlanesSay ρ W h K3 s.pM
  sD : PlanesSay ρ W h K3 s.pD
  uM : UnitAt ρ W h K3 s.kM (h.t.score.getD 0 default) s.cM
  uD : UnitAt ρ W h K3 s.kD (h.t.score.getD 1 default) s.cD
  iM : InUnit h s.kM (h.t.score.getD 0 default)
  iD : InUnit h s.kD (h.t.score.getD 1 default)
  nM : s.pM.np = 3
  nD : s.pD.np = 3
  nUM : s.cM.np = 5
  nUD : s.cD.np = 5
  s0M : s.cM.s0 = s.kM.s0
  s0D : s.cD.s0 = s.kD.s0

/-- The verifier's points and weights are the library's: at the lookup's end point. -/
structure PtsAre (ρ : Reading Kf) (h : Attention.Heard) (P : OwnPar Kf M X) (u : P.Run) (s : Six) : Prop where
  pM : PlanePts ρ h P.D P.C (zT u) .m1 s.pM
  pD : PlanePts ρ h P.D P.C (zT u) .d1 s.pD
  cM : PlanePts ρ h P.D P.C (zT u) .m2 s.cM
  cD : PlanePts ρ h P.D P.C (zT u) .d2 s.cD
  xM : MaxIs ρ h P.D P.C (zT u) .m2 (zg P.D P.C (zT u)) s.kM
  xD : MaxIs ρ h P.D P.C (zT u) .d2 (zgD P.D P.C (zT u)) s.kD
  dv : DivIs ρ h P.D P.C (zT u)

/-- The output statements' points and challenges are the verifier's; the lengths of what was drawn. -/
structure OutsAre (ρ : Reading Kf) (h : Attention.Heard) (P : OwnPar Kf M X) (u : P.Run) (s : Six) : Prop where
  rM : s.kM.sc.r.size = P.D.lg + P.D.lP + (P.D.lP + 1) + h.S.cf.ldh
  xM : ∀ j < P.D.lg + P.D.lP + (P.D.lP + 1) + h.S.cf.ldh, ptN P.uM.T u.oM j = pt ρ s.kM.sc.r j
  rD : s.kD.sc.r.size = P.D.lg + (P.D.lP + 1) + h.S.cf.ldh
  xD : ∀ j < P.D.lg + (P.D.lP + 1) + h.S.cf.ldh, ptN P.uD.T u.oD j = pt ρ s.kD.sc.r j
  rE : h.S.cf.lgk ≤ h.d.scE.r.size
  xE : ∀ j < h.S.cf.lgk, ptN P.sE.T u.oE j = pt ρ h.d.scE.r j
  ynE : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = yn P.D P.C (Pub.z u.oE.st) j
  rVM : h.S.cf.lgk ≤ h.d.vpm.r.size
  xVM : ∀ j < h.S.cf.lgk, ptN P.sVM.T u.oVM j = pt ρ h.d.vpm.r j
  ptVM : ∀ j < h.S.nM - h.S.cf.lmS, pt ρ h.t.ptM j = ptBelow P.D P.C u.oVM.st (ptN P.sVM.T u.oVM) j
  ynVM : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = yn P.D P.C (Pub.z u.oVM.st) j
  thVM : ρ.val h.d.gam = Pub.th u.oVM.st
  rVD : h.S.cf.lgk ≤ h.d.vpd.r.size
  xVD : ∀ j < h.S.cf.lgk, ptN P.sVD.T u.oVD j = pt ρ h.d.vpd.r j
  ptVD : ∀ j < h.S.nD - h.S.cf.lmS, pt ρ h.t.ptD j = ptOn P.D P.C u.oVD.st (ptN P.sVD.T u.oVD) j
  ynVD : ∀ j < h.S.cf.ldh, pt ρ h.d.zcW j = yn P.D P.C (Pub.z u.oVD.st) j
  thVD : ρ.val h.d.gam = Pub.th u.oVD.st
  th : ρ.val h.d.gam = u.th
  tg : h.x.tg.size = h.S.cf.lgk
  vtg : ∀ j < h.S.cf.lgk, pt ρ h.x.tg j = (P.pubZ u.z).tg j
  rF : h.x.scF.r.size = h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh
  xF : ∀ j < h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh, ptN P.sF.T u.oF j = pt ρ h.x.scF.r j
  rK : h.x.scd.r.size = 2 * h.S.cf.lt + h.S.cf.lgk
  xK : ∀ j < 2 * h.S.cf.lt + h.S.cf.lgk, ptN P.sD.T u.oK j = pt ρ h.x.scd.r j
  fn : ∀ j < h.S.cf.ldh, pt ρ (h.x.rc h.S) j = (Prod.fst u.oK.st).fn j
  rH : h.x.scH.r.size = h.S.cf.lt + h.S.cf.lgk + 4
  xH : ∀ j < h.S.cf.lt + h.S.cf.lgk + 4, ptN P.sH.T u.oH j = pt ρ h.x.scH.r j

/-- The dictionary of slots, in the numbers of the record h. x: the early and the late entries. -/
structure SlotsH (W : World Kf) (h : Attention.Heard) (P : OwnPar Kf M X) (u : P.Run) (m : M) (s : Six)
    (ul : J₂ → Kf) : Prop where
  m1 : ∀ j : Fin (3 * P.npl + 7), j.val < 3 → W.slot (s.pM.s0 + j.val) = u.rM j - P.msg m (P.kM j)
  m2 : ∀ j : Fin (3 * P.npl + 7), 3 ≤ j.val → j.val < 6 →
    W.slot (s.pD.s0 + (j.val - 3)) = u.rM j - P.msg m (P.kM j)
  m3 : ∀ j : Fin (3 * P.npl + 7), 6 ≤ j.val → W.slot (s.kM.s0 + (j.val - 6)) = u.rM j - P.msg m (P.kM j)
  d : ∀ j : Fin 7, W.slot (s.kD.s0 + j.val) = u.rD j - P.msg m (P.kD j)
  e : ∀ j : Fin (5 + P.D.lT + 2), W.slot (slotEh h P.D.lT j.val) = u.rE j - P.msg m (P.kE j)
  v0 : W.slot h.d.sCl = u.rV 0 - P.msg m (P.kV 0)
  v1 : W.slot (h.d.sCl + 1) = u.rV 1 - P.msg m (P.kV 1)
  f : ∀ b : Fin P.D.nb, W.slot (h.x.sM6 + b.val) = u.s b - P.msg m (P.kF b)
  eM : ∀ b : Fin P.D.nb,
    SlotAt W P.uM.T u.oM (Sum.elim (P.msg m) ul) (s.kM.sc.sEnd + 2 * b.val) (b, false) ∧
    SlotAt W P.uM.T u.oM (Sum.elim (P.msg m) ul) (s.kM.sc.sEnd + (2 * b.val + 1)) (b, true)
  eD : ∀ b : Fin P.D.nb,
    SlotAt W P.uD.T u.oD (Sum.elim (P.msg m) ul) (s.kD.sc.sEnd + 2 * b.val) (b, false) ∧
    SlotAt W P.uD.T u.oD (Sum.elim (P.msg m) ul) (s.kD.sc.sEnd + (2 * b.val + 1)) (b, true)
  eE : ∀ b : Fin P.D.nb,
    SlotAt W P.sE.T u.oE (Sum.elim (P.msg m) ul) (h.d.scE.sEnd + 2 * b.val) (b, false) ∧
    SlotAt W P.sE.T u.oE (Sum.elim (P.msg m) ul) (h.d.scE.sEnd + (2 * b.val + 1)) (b, true)
  eVM : ∀ b : Fin P.D.nb,
    SlotAt W P.sVM.T u.oVM (Sum.elim (P.msg m) ul) (h.d.vpm.sEnd + 2 * b.val) (b, false) ∧
    SlotAt W P.sVM.T u.oVM (Sum.elim (P.msg m) ul) (h.d.vpm.sEnd + (2 * b.val + 1)) (b, true)
  eVD : ∀ b : Fin P.D.nb,
    SlotAt W P.sVD.T u.oVD (Sum.elim (P.msg m) ul) (h.d.vpd.sEnd + 2 * b.val) (b, false) ∧
    SlotAt W P.sVD.T u.oVD (Sum.elim (P.msg m) ul) (h.d.vpd.sEnd + (2 * b.val + 1)) (b, true)
  eF : ∀ b : Fin P.D.nb,
    SlotAt W P.sF.T u.oF (Sum.elim (P.msg m) ul) (h.x.scF.sEnd + 2 * b.val) (b, false)
  eK : ∀ l : Fin (size18 P.D).Lam, SlotAt W P.sD.T u.oK (Sum.elim (P.msg m) ul) (h.x.sKC + l.val) (.inl l)
  eB : ∀ (b : Fin (size18 P.D).pairs) (t : Fin (size18 P.D).lt),
    SlotAt W P.sD.T u.oK (Sum.elim (P.msg m) ul) (h.x.sIb h.S b.val t.val) (.inr (b, t))
  eH : ∀ b : Fin P.D.nb,
    SlotAt W P.sH.T u.oH (Sum.elim (P.msg m) ul) (h.x.scH.sEnd + 2 * b.val) (b, false) ∧
    SlotAt W P.sH.T u.oH (Sum.elim (P.msg m) ul) (h.x.scH.sEnd + (2 * b.val + 1)) (b, true)

/-- The eight sumchecks' first output claims: on the rows. -/
structure RowsHold (P : OwnPar Kf M X) (u : P.Run) (m : M) : Prop where
  rM : P.uM.T.our.par.UHolds u.oM (P.msg m)
  rD : P.uD.T.our.par.UHolds u.oD (P.msg m)
  rE : P.sE.T.our.par.UHolds u.oE (P.msg m)
  rVM : P.sVM.T.our.par.UHolds u.oVM (P.msg m)
  rVD : P.sVD.T.our.par.UHolds u.oVD (P.msg m)
  rF : P.sF.T.our.par.UHolds u.oF (P.msg m)
  rK : P.sD.T.our.par.UHolds u.oK (P.msg m)
  rH : P.sH.T.our.par.UHolds u.oH (P.msg m)

/-- **port_cl: the library's ledger of the own rounds' claims holds, at the late entries read off the world.** -/
theorem port_cl {h : Attention.Heard} (s : Six) (Z : SizesAre P L h) (A : AttPub ρ h lid cf fs) (F : Fits L Q)
    (N : ShapeNums P h) (Sy : Say ρ W h K3) (S6 : SixSay ρ W h K3 s) (I : InTail h)
    (Pt : PtsAre ρ h P u s) (O : OutsAre ρ h P u s)
    (Sl : SlotsH W h P u m s (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S))) (R : RowsHold P u m)
    (hj : (joinF (J₂ := J₂) Q u).Holds
      (Sum.elim (P.msg m) (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S)))) :
    ∀ f ∈ ownCl L Q u, f.Holds (Sum.elim (P.msg m) (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S))) := by
  have LA := late_at W h K3 L.Y (tabOfAtt h) (placeAtt h.S)
  have Tb := lateTabs_att h
  have e2 : W.slot h.d.sACC = u.rE P.iACC - P.msg m (P.kE P.iACC) := by
    have e := Sl.e P.iACC
    unfold slotEh at e
    rw [if_pos (by show (0 : ℕ) < 5; norm_num)] at e
    exact e
  have e3 : W.slot h.d.sZC = u.rE P.iZC - P.msg m (P.kE P.iZC) := by
    have e := Sl.e P.iZC
    unfold slotEh at e
    rw [if_pos (by show (2 : ℕ) < 5; norm_num)] at e
    exact e
  exact ownCl_of_parts
    (clM0_holds Z A LA F.gLin rfl rfl S6.sM S6.sD S6.uM Pt.pM Pt.pD Pt.cM S6.nM S6.nD S6.nUM S6.s0M Pt.xM
      Sl.m1 Sl.m2 Sl.m3)
    (clM_holds Z A LA rfl rfl S6.uM S6.iM Pt.xM.pairs N.q2 N.k2 O.rM O.xM F.g6b Sl.eM
      ((rowF_holds _ _ _).2 R.rM))
    (clD0_holds Z A LA F.gLin rfl rfl S6.uD Pt.cD S6.nUD S6.s0D Pt.xD Sl.d)
    (clD_holds Z A LA rfl rfl S6.uD S6.iD Pt.xD.pairs N.q2 N.k2 O.rD O.xD F.g6d Sl.eD
      ((rowF_holds _ _ _).2 R.rD))
    (clE0_holds Z A LA F.gLin rfl rfl rfl Sy.s5 Pt.dv Sl.e)
    (clE_holds Z A LA rfl rfl Sy.s5 I Pt.dv.pW N.o2 O.rE Pt.dv.cW O.xE O.ynE F.g8 Sl.eE
      ((rowF_holds _ _ _).2 R.rE))
    hj
    (lineF_holds Sy.s6 Sl.v0 Sl.v1 e2 e3 O.th)
    (clVM_holds Z A LA rfl rfl Sy.s6 I Pt.dv.pW N.v2 N.nM N.ptM O.rVM Pt.dv.cW O.xVM O.ptVM O.ynVM O.thVM
      F.g11 Sl.eVM ((rowF_holds _ _ _).2 R.rVM))
    (clVD_holds Z A LA Tb Sy.s6 I Pt.dv.pW N.v2 N.nD N.ptD O.rVD Pt.dv.cW O.xVD O.ptVD O.ynVD O.thVD
      F.g12 Sl.eVD ((rowF_holds _ _ _).2 R.rVD))
    (clM6_holds Z A LA Tb Sy.s7 O.tg O.vtg F.gM Sl.f)
    (clF_holds Z A LA Tb Sy.s7 I N.q2 O.rF O.xF F.g16 Sl.eF ((rowF_holds _ _ _).2 R.rF))
    (clK_holds Z A LA Tb Sy.s7 I N.k2 O.rF O.rK O.xK O.fn F.g18 Sl.eK Sl.eB ((rowF_holds _ _ _).2 R.rK))
    (clH_holds Z A LA Tb Sy.s8 O.rH O.xH F.gH Sl.eH ((rowF_holds _ _ _).2 R.rH))

/-- **The same for the pull-backs**, under the library's Agree: each late entry read off the world is worth its meant form. -/
theorem port_pull {h : Attention.Heard} (s : Six) (Z : SizesAre P L h) (A : AttPub ρ h lid cf fs) (F : Fits L Q)
    (N : ShapeNums P h) (Sy : Say ρ W h K3) (S6 : SixSay ρ W h K3 s) (I : InTail h)
    (Pt : PtsAre ρ h P u s) (O : OutsAre ρ h P u s)
    (Sl : SlotsH W h P u m s (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S))) (R : RowsHold P u m)
    (hj : (joinF (J₂ := J₂) Q u).Holds
      (Sum.elim (P.msg m) (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S))))
    (hA : Cb.Sub.Agree (attA L u) (P.msg m) (uAt W h K3 L.Y (tabOfAtt h) (placeAtt h.S))) :
    ∀ f ∈ ownCl L Q u, (Cb.Sub.pullF (attA L u) f).Holds (P.msg m) :=
  ownCl_pull_of_agree hA (port_cl s Z A F N Sy S6 I Pt O Sl R hj)

end K5Law
