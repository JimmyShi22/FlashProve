-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/AgreeTop.lean: kind K5: "the tables are true", typed, at a record of
the kind's own: h := oldOf S gL i (Johnson/Desc/First/Att/Claims/Any.lean).

Main names:
  `RunIs ρ h kM kD C X`: what the run made of what was heard gives: the five states' z are the
    lookup's end point; the eight sumchecks' points are the verifier's challenges, with their
    lengths; ti; fn; the two points on the regions' entries. Not shown in this file or in what it
    imports.
  `xi_of`: XiIs (Johnson/Desc/First/Att/Claims/WeightsOf.lean), from TieM, TieD, Tie5 and Look
    (Johnson/Desc/First/Att/Claims/PointsTieU.lean, PointsTie.lean), PubA
    (Johnson/Desc/First/Att/Claims/PointsMore.lean) and RunIs. `weights_are`: WeightsAre at attTb L
    u. `scores_two`.
  `agree_top`: Cb.Sub.Agree (attA L u) (P.msg m) (uAt W h K3 L.Y (tabOfAtt h) (placeAtt S)).
Premises of agree_top: AttAt (every table of the list is true of the matrices M in W; the list of
matrices fits; shapeHid's yes; Numerals) and CellsTie: the smallness test's kind's; LookAll and
KeyIs at the point lk.zx at which the tables were made: the lookup's kind's; RunIs and SizesAre: the
hearing's; PlanLaw (Johnson/Desc/First/Att/Claims/PlanLaw.lean); P.C = callsOf fs; the return of
pointsOf and tablesP; every late entry's name is listed. None of these is shown in this file or in
what it imports.
Limit: UsualCalls (in PlanLaw) is no test of the verifier: at another call list this file says
nothing.
Of OnBytes and Johnson/Road no routine that runs in a context is named, and no theorem on such a
routine's return; the runs spoken of are the kind's own (Johnson/Desc/First/Att/RunsP.lean).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.WeightsOf
import Johnson.Desc.First.Att.Claims.PlacesIn
import Johnson.Desc.First.Att.Claims.KeyPubOf
import Johnson.Desc.First.Att.Claims.PointsMore
import Johnson.Desc.First.Att.Claims.PlanLaw

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Cb.Pv.Att
open Inst.Model.AttSeg (Calls Pub)
open Cb.Pv.Att.End (AttTab EndLay attTb attA ptOn namesOf)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ScoreP LookIn geoOf)

variable {Kf : Type} [Field Kf]

/-- **What the run made of what was heard gives**: the five states' z are the lookup's end point; the eight sumchecks' points are the verifier's challenges, with their lengths; the drawn point's part ti; the score's point's part fn; the two points on the regions' entries. -/
structure RunIs (ρ : Reading Kf) (h : Attention.Heard) (kM kD : Score) (C : Calls) (X : Xi Kf) : Prop where
  zM : X.zM = X.z
  zD : X.zD = X.z
  zE : X.zE = X.z
  zVM : X.zVM = X.z
  zVD : X.zVD = X.z
  rM : kM.sc.r.size = h.S.cf.lgk + 2 * h.S.lnT - 1 + h.S.cf.ldh
  pM : ∀ j, X.xM j = pt ρ kM.sc.r j
  rD : kD.sc.r.size = h.S.cf.lgk + h.S.lnT + h.S.cf.ldh
  pD : ∀ j, X.xD j = pt ρ kD.sc.r j
  rE : h.d.scE.r.size = h.S.cf.lgk + h.S.cf.lt
  pE : ∀ j, X.xE j = pt ρ h.d.scE.r j
  rVM : h.d.vpm.r.size = h.S.cf.lgk + 2 * h.S.lnT - 1 + h.S.cf.lB
  pVM : ∀ j, X.xVM j = pt ρ h.d.vpm.r j
  rVD : h.d.vpd.r.size = h.S.cf.lgk + h.S.lnT + h.S.cf.lB
  pVD : ∀ j, X.xVD j = pt ρ h.d.vpd.r j
  rF : h.x.scF.r.size = h.S.cf.lt + h.S.cf.lgk + h.S.cf.ldh
  pF : ∀ j, X.xF j = pt ρ h.x.scF.r j
  rK : h.x.scd.r.size = 2 * h.S.cf.lt + h.S.cf.lgk
  pK : ∀ j, X.xK j = pt ρ h.x.scd.r j
  rH : h.S.cf.lt ≤ h.x.scH.r.size
  pH : ∀ j, X.xH j = pt ρ h.x.scH.r j
  sti : h.x.ti.size = h.S.cf.lt
  ti : ∀ j < h.S.cf.lt, pt ρ h.x.ti j = X.ti j
  fn : ∀ j < h.S.cf.ldh, pt ρ (h.x.rc h.S) j = X.fn j
  sPM : h.t.ptM.size = h.S.nM
  ptM : ∀ j < h.S.nM, pt ρ h.t.ptM j = ptBelow (L5.dimOf h.S) C X.stVM X.xVM j
  sPD : h.t.ptD.size = h.S.nD
  ptD : ∀ j < h.S.nD, pt ρ h.t.ptD j = ptOn (L5.dimOf h.S) C X.stVD X.xVD j

variable {ρ : Reading Kf} {S : Attention.Shape} {fs : Model.Forest.Shape} {zx : Array E} {p : Pub Kf}
  {gL : Forest.Heard} {i : P.Runs.In} {k1 k2 : ScoreP} {X : Xi Kf}

/-- **XiIs**, from the ties at the lookup's point and what the run gives. -/
theorem xi_of {lid : ℕ} {cf : Attention.Cfg} (hid : shapeHid lid cf = Except.ok (S, fs))
    (hF : L5.CallsFit S fs) (L : Look ρ fs zx p) (T1 : TieM ρ S fs k1 p) (T2 : TieD ρ S fs k2 p)
    (T5 : Tie5 ρ S fs i.p.d p) (b1 : k1.below = true) (b2 : k2.below = false)
    (PA : PubA (oldOf S gL i)) (hz : X.z = p.z)
    (R : RunIs ρ (oldOf S gL i) (scoreBack k1) (scoreBack k2) (L5.callsOf fs) X) :
    XiIs ρ (oldOf S gL i) (scoreBack k1) (scoreBack k2) zx (L5.callsOf fs) X := by
  have N := norm_of_hid hid
  have Z := sizes_of_hid hid
  have hM : S.cf.lmS ≤ S.nM := lmS_le_nM S N Z
  have eM : (L5.dimOf S).lM = S.nM := N.nM.symm
  have hle := fam_le hF L .m1
  have hle' : (L5.dimOf S).lM ≤ zx.size := hle
  have hT : (L5.dimOf S).T = S.T := by rw [(L5.dimOf S).T_eq, Z.T]; congr 1; exact N.lt.symm
  exact {
    nums := ⟨Z, N.lt.symm, hT⟩
    zM := R.zM, zD := R.zD, zE := R.zE, zVM := R.zVM, zVD := R.zVD
    wIM := by rw [hz]; exact T1.wI
    siM := T1.si, iM := by rw [hz]; exact T1.i
    sjM := T1.sj, jM := by rw [hz]; exact T1.j
    wID := by rw [hz]; exact T2.wI
    siD := T2.si, iD := by rw [hz]; exact T2.i
    sjD := T2.sj, jD := by rw [hz]; exact T2.j
    siW := T5.siW, iW := by rw [hz]; exact T5.iW
    siX := T5.siX, iX := by rw [hz]; exact T5.iX
    scW := T5.scW, nW := by rw [hz]; exact T5.nW
    sA := by show S.cf.lmS ≤ zx.size; omega
    vA := fun j hj => by
      have hj' : j < S.cf.lmS := hj
      rw [hz]
      show pt ρ zx (zx.size - S.cf.lmS + j) =
        Inst.Model.AttSeg.inn (L5.dimOf S) (L5.callsOf fs) p.z .m1 ((L5.dimOf S).lM - S.cf.lmS + j)
      rw [inn_zx hF L .m1 (by show (L5.dimOf S).lM - S.cf.lmS + j < (L5.dimOf S).lM; omega)]
      congr 1
      show zx.size - S.cf.lmS + j = zx.size - (L5.dimOf S).lM + ((L5.dimOf S).lM - S.cf.lmS + j)
      omega
    segM := by show (if k1.below then Attention.Seg.fm else Attention.Seg.fd) = _; rw [b1]; rfl
    segD := by show (if k2.below then Attention.Seg.fm else Attention.Seg.fd) = _; rw [b2]; rfl
    rM := R.rM, pM := R.pM, rD := R.rD, pD := R.pD, rE := R.rE, pE := R.pE, rVM := R.rVM, pVM := R.pVM
    rVD := R.rVD, pVD := R.pVD, rF := R.rF, pF := R.pF, rK := R.rK, pK := R.pK, rH := R.rH, pH := R.pH
    wJv := PA.wJv, sti := R.sti, ti := R.ti, fn := R.fn, nM := eM, nD := N.nD.symm, lmM := hM
    sPM := R.sPM, ptM := R.ptM, sPD := R.sPD, ptD := R.ptD }

/-- **WeightsAre, paid**, at parameters whose sizes are the shape's. -/
theorem weights_are [Fintype Kf] {Mg Xx J₂ : Type} {P : OwnPar Kf Mg Xx} {L : EndLay P J₂} {u : P.Run}
    {h : Attention.Heard} {kM kD : Score} (Z : SizesAre P L h) (I : XiIs ρ h kM kD zx P.C (xiOf u)) :
    WeightsAre ρ h kM kD zx (attTb L u) := by
  rw [attTb_eq, Z.D, Z.ls, Z.lmS]
  exact weights_at I

variable {c0 c1 c2 c3 : ACall} {zk : Array (Array E)} {hh : P.Heard} {L' : P.Left}

/-- At a place with the four calls there are just two units. -/
theorem scores_two (Pl : PlaceIs S c0 c1 c2 c3) (hP : P.pointsOf (geoOf S) zk hh L' = some i.p)
    (hk1 : i.p.scores[0]? = some k1) (hk2 : i.p.scores[1]? = some k2) : i.p.scores.toList = [k1, k2] := by
  have PA := points_are hP
  obtain ⟨_, _, nS⟩ := points_counts hP
  have nH : hh.scores.size = 2 := by rw [← PA.nH, place_scores Pl]; rfl
  exact list_two (by rw [Array.length_toList, nS, nH]) (by rw [Array.getElem?_toList]; exact hk1)
    (by rw [Array.getElem?_toList]; exact hk2)

open OnBytes.Road.L5 (callAt)

/-- **"The tables are true", typed, at a record of the kind's own.** What is left as premises: of the smallness test's kind: every table of the list is true of the matrices M in W and the list of matrices fits (AttAt), and the cells of the message are M's (CellsTie); of the lookup's kind: LookAll and KeyIs; of the hearing: RunIs and SizesAre; the plan facts PlanLaw; the calls' letters hC; every late entry's name is listed (hY). -/
theorem agree_top [Fintype Kf] {Mg Xx J₂ : Type} [Fintype J₂] [DecidableEq J₂] {Pp : OwnPar Kf Mg Xx}
    {L : EndLay Pp J₂} {u : Pp.Run} {m : Mg} {W : World Kf} {tl : HTailF2} {K3 : ℕ} {M : Mats Kf} {lid : ℕ}
    {cf : Attention.Cfg} {zy : Array E} {nW : ℕ} {lk : LookIn}
    (PL : PlanLaw cf S fs) (Lk : LookAll ρ fs lk.zx zy (Pp.pub0 u.y0))
    (hK : ∀ q : Fin 4, KeyIs fs lk.zx zy (zk.getD q.val #[]) q) (hg : i.g = geoOf S)
    (hP : P.pointsOf i.g zk hh L' = some i.p)
    (ht : P.tablesP i.g (matsOf tl.mats) nW lk i.p = some i.t)
    (hk1 : i.p.scores[0]? = some k1) (hk2 : i.p.scores[1]? = some k2)
    (Z : SizesAre Pp L (oldOf S gL i)) (hC : Pp.C = L5.callsOf fs)
    (A : AttAt ρ W tl K3 M (oldOf S gL i) lid cf fs)
    (R : RunIs ρ (oldOf S gL i) (scoreBack k1) (scoreBack k2) (L5.callsOf fs) (xiOf u))
    (Ct : CellsTie (oldOf S gL i) M L.cellJ (Pp.msg m))
    (hY : ∀ j, (L.Y.nm j).2 ∈ namesOf (L5.dimOf S) S.ls S.cf.lmS (L.Y.nm j).1) :
    Cb.Sub.Agree (attA L u) (Pp.msg m)
      (uAt W (oldOf S gL i) K3 L.Y (tabOfAtt (oldOf S gL i)) (placeAtt S)) := by
  have hid : shapeHid lid cf = Except.ok (S, fs) := A.shape
  have hp : PosG i.g := by rw [hg]; exact PL.pos
  have PA := pub_a (gL := gL) hg (points_more hP)
  have Tb := tabs_at (gL := gL) hg ht hp
  rw [hg] at hP
  obtain ⟨T1, T2, T5, b1, b2, _, _⟩ := ties_of hid PL.fit Lk hK PL.place hP hk1 hk2
  have hs := scores_two PL.place hP hk1 hk2
  have hs' : (oldOf S gL i).scores.toList = [scoreBack k1, scoreBack k2] := by
    show (i.p.scores.map scoreBack).toList = _
    rw [Array.toList_map, hs]
    rfl
  have I := xi_of (gL := gL) hid PL.fit (look_of Lk) T1 T2 T5 b1 b2 PA (X := xiOf u) rfl R
  rw [← hC] at I
  exact agree_of_attAt Z A Tb (score_tabs Tb hs') (weights_are Z I) (places_in hid hg ht hp hs) Ct hY

end K5Law
