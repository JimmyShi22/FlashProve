-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/KeysPubAll.lean: kind K5: the last joint: LinPub
(Johnson/Desc/First/Att/Claims/KeysWorth.lean), the record of public premises under which the key
forms' named scalars have their rule values, AT WHAT pointsOf MAKES, with the table clauses alone
left as premises.

Main names:
  `LinTabs tl h pM pD cM cD kM kD tM tD`: the ten table clauses of LinPub: the table on "as" at the
    four plane claims' own last coordinates; the two units' tables on the maxima; hW; hX; tO at the
    points of wl and of wh. A premise here: Johnson/Desc/First/Att/Claims/KeysTabs.lean draws it
    out of TabsAt (Johnson/Desc/First/Att/Claims/TablesAt.lean).
  `unitsOf`: the record Units of Johnson/Road/Rows out of the kind's own records.
  `linPub_of`: **Ground ∧ pointsOf (geoOf S) zk hh L = some i.p ∧ pM, pD are plane claims of the
    record with three planes, below | on the diagonal ∧ kM, kD are units of the record below | on
    the diagonal, with the plane claims cM, cD ∧ LinTabs ⟹ LinPub ρ tl (oldOf S gL i) (unitsOf …)
    (remBack cM) (remBack cD) (callsOf fs) p.**
Ground (Johnson/Desc/First/Att/Claims/KeysPub.lean): the planner's shape at the usual call list;
CallsFit; each call's key point is the lookup's cut of its end point; the library's z is that end
point, read.
Used: KeysPub.lean, PointsTie.lean, PointsTieU.lean, PointsCut.lean, PiecesTie.lean, LookKeys.lean.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.KeysPub

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.Road.L5 (callAt FourCalls UsualCalls)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo Pts ScoreP RemP UnitG CallG geoOf callOf keysOf)
open Inst.Model.AttSeg (Pub Fam wp inn)

variable {Kf : Type} [Field Kf]

/-- The table clauses of LinPub. -/
structure LinTabs (tl : HTailF2) (h : Attention.Heard) (pM pD cM cD : RemP) (kM kD : ScoreP)
    (tM tD : ScoreTables) : Prop where
  aM1 : AsAt h h.t.tA (lastN pM.z h.S.cf.lmS)
  aD1 : AsAt h h.t.tA (lastN pD.z h.S.cf.lmS)
  aM2 : AsAt h h.t.tA (lastN cM.z h.S.cf.lmS)
  aD2 : AsAt h h.t.tA (lastN cD.z h.S.cf.lmS)
  mM : TabAt tl h tM.tM h.S.cf.NAs h.S.T (Attention.tok h.S kM.wI kM.zi)
  mD : TabAt tl h tD.tM h.S.cf.NAs h.S.T (Attention.tok h.S kD.wI kD.zi)
  hW : TabAt tl h h.t.hW h.S.cf.NAs h.S.T (eqTab h.d.ziW)
  hX : TabAt tl h h.t.hX h.S.cf.NAs h.S.T (eqTab h.d.ziX)
  oW : TabAt tl h h.t.tO (h.S.cf.NAs + 1) (2 ^ h.S.cf.la)
    (blockRows (lowOf h.S h.d.zcW) (eqTab h.d.ziW))
  oH : TabAt tl h h.t.tO (h.S.cf.NAs + 1) (2 ^ h.S.cf.la)
    (blockRows (lowOf h.S h.d.zcH) (eqTab h.d.ziH))

/-- The four units, as Johnson/Road/Rows has them. -/
def unitsOf (pM pD : RemP) (kM kD : ScoreP) (tM tD : ScoreTables) : Units :=
  ⟨remBack pM, remBack pD, scoreBack kM, scoreBack kD, tM, tD⟩

variable {ρ : Reading Kf} {lid : ℕ} {cf : Cfg} {S : Attention.Shape} {fs : Model.Forest.Shape}
  {zx zy : Array E} {zk : Array (Array E)} {p : Pub Kf} {gL : Forest.Heard} {i : P.Runs.In}
  {tl : HTailF2}

theorem np_pos (hid : shapeHid lid cf = Except.ok (S, fs)) : 0 < S.NP := by
  have P := L5.shaped_of_hid hid
  show 0 < S.Lam * S.HA
  rw [P.Lam, P.HA]
  exact Nat.mul_pos (Nat.two_pow_pos _) (L5.tests_of_hid hid).2

theorem ends_single (G : Ground ρ lid cf S fs zx zy zk p) (u : UnitG)
    (hu : ∃ k, (geoOf S).single k = some u) : EndsIn (zk.getD u.call #[]) zx := by
  obtain ⟨k, hk⟩ := hu
  obtain ⟨q, c, hc, rfl⟩ := single_at hk
  have hm : (c, q) ∈ (geoOf S).calls.toList.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simpa using hc
  obtain ⟨hq, _⟩ := call_at (L5.four_of_hid G.hid G.usual) hm
  exact endsIn_of (G.keys ⟨q, hq⟩)

/-- The pieces of the three lists that one call alone serves. -/
theorem three_old (G : Ground ρ lid cf S fs zx zy zk p) {P' : Pts} (H : Cut5w (geoOf S) zk P') :
    pwBack P'.d.pwW = pieces (callAt S 2) (zk.getD 2 #[]) .wl ∧
    pwBack P'.d.pwX = pieces (callAt S 2) (zk.getD 2 #[]) .ix ∧
    pwBack P'.d.pwH = pieces (callAt S 3) (zk.getD 3 #[]) .wh := by
  have Fo := L5.four_of_hid G.hid G.usual
  have hp := np_pos G.hid
  obtain ⟨uW, uX, uH, hW, hX, hH, eW, eX, eH, sW, sX, sH⟩ := H.at'
  have sW' : P'.d.pwW.size = S.NP := sW
  have sX' : P'.d.pwX.size = S.NP := sX
  have sH' : P'.d.pwH.size = S.NP := sH
  refine ⟨?_, ?_, ?_⟩
  · rw [eW]
    refine (single_old Fo (s := .wl) (q0 := 2) (fun q hq hne => ?_) hW zk
      (by rw [← eW, sW']; exact hp)).2
    interval_cases q
    · exact mem_two rfl rfl Fo.p0
    · exact mem_two rfl rfl Fo.p1
    · exact absurd rfl hne
    · rw [Fo.p3]; exact fam_other rfl _ _ _ _
  · rw [eX]
    refine (single_old Fo (s := .ix) (q0 := 2) (fun q hq hne => ?_) hX zk
      (by rw [← eX, sX']; exact hp)).2
    interval_cases q
    · exact mem_two rfl rfl Fo.p0
    · exact mem_two rfl rfl Fo.p1
    · exact absurd rfl hne
    · rw [Fo.p3]; exact fam_other rfl _ _ _ _
  · rw [eH]
    refine (single_old Fo (s := .wh) (q0 := 3) (fun q hq hne => ?_) hH zk
      (by rw [← eH, sH']; exact hp)).2
    interval_cases q
    · exact mem_two rfl rfl Fo.p0
    · exact mem_two rfl rfl Fo.p1
    · exact mem_two rfl rfl Fo.p2
    · exact absurd rfl hne

/-- **LinPub at what pointsOf makes**, the table clauses alone left. -/
theorem linPub_of (G : Ground ρ lid cf S fs zx zy zk p) {hh : P.Heard} {L' : P.Left}
    (hp : P.pointsOf (geoOf S) zk hh L' = some i.p) {pM pD cM cD : RemP} {kM kD : ScoreP}
    {tM tD : ScoreTables}
    (mM : pM ∈ i.p.planes.toList) (fM : pM.isD = false) (nM : pM.np = 3)
    (mD : pD ∈ i.p.planes.toList) (fD : pD.isD = true) (nD : pD.np = 3)
    (uM : kM ∈ i.p.scores.toList) (bM : kM.below = true) (qM : i.p.planes[kM.claim]? = some cM)
    (uD : kD ∈ i.p.scores.toList) (bD : kD.below = false) (qD : i.p.planes[kD.claim]? = some cD)
    (T : LinTabs tl (oldOf S gL i) pM pD cM cD kM kD tM tD) :
    LinPub ρ tl (oldOf S gL i) (unitsOf pM pD kM kD tM tD) (remBack cM) (remBack cD)
      (L5.callsOf fs) p := by
  have Fo := L5.four_of_hid G.hid G.usual
  have N := norm_of_hid G.hid
  have Z := sizes_of_hid G.hid
  have L := look_of G.look
  have CU := cutU_of hp
  obtain ⟨F1, F2, F3, F4, F5, F6, F7⟩ := seven_of_hid ρ G.hid G.usual p
  have T5 := tie5_of G.fit L N.lt (ends_single G) (cut5_of hp)
  obtain ⟨w5, x5, h5⟩ := three_old G (cut5w_of hp)
  -- the units' plane claims
  obtain ⟨c1, e1, U1⟩ := CU.units kM uM
  obtain ⟨c2, e2, U2⟩ := CU.units kD uD
  have ec1 : c1 = cM := Option.some.inj (e1.symm.trans qM)
  have ec2 : c2 = cD := Option.some.inj (e2.symm.trans qD)
  subst ec1 ec2
  have mc1 : c1 ∈ i.p.planes.toList := by
    rw [Array.mem_toList_iff]
    exact Array.mem_of_getElem? e1
  have mc2 : c2 ∈ i.p.planes.toList := by
    rw [Array.mem_toList_iff]
    exact Array.mem_of_getElem? e2
  have A1 := CU.planes pM mM
  have A2 := CU.planes pD mD
  have A3 := CU.planes c1 mc1
  have A4 := CU.planes c2 mc2
  have f3 : c1.isD = false := by rw [U1.isD, bM]; rfl
  have f4 : c2.isD = true := by rw [U2.isD, bD]; rfl
  -- each claim's call and pieces
  have o1 : pM.call = 0 ∧ (remBack pM).pw = pieces (callAt S 0) (zk.getD 0 #[]) .rm := by
    rcases plane_old Fo A1 with ⟨_, a, b⟩ | ⟨a, _, _⟩
    · rw [fM] at b; exact ⟨a, b⟩
    · omega
  have o2 : pD.call = 0 ∧ (remBack pD).pw = pieces (callAt S 0) (zk.getD 0 #[]) .rd := by
    rcases plane_old Fo A2 with ⟨_, a, b⟩ | ⟨a, _, _⟩
    · rw [fD] at b; exact ⟨a, b⟩
    · omega
  have o3 : c1.call = 1 ∧ (remBack c1).pw = pieces (callAt S 1) (zk.getD 1 #[]) .fm := by
    rcases plane_old Fo A3 with ⟨a, _, _⟩ | ⟨_, a, b⟩
    · have := U1.np; omega
    · rw [f3] at b; exact ⟨a, b⟩
  have o4 : c2.call = 1 ∧ (remBack c2).pw = pieces (callAt S 1) (zk.getD 1 #[]) .fd := by
    rcases plane_old Fo A4 with ⟨a, _, _⟩ | ⟨_, a, b⟩
    · have := U2.np; omega
    · rw [f4] at b; exact ⟨a, b⟩
  have P1 := planeM_at (gL := gL) (i := i) G A1 fM (q := 0) o1.1 o1.2 F1 rfl rfl T.aM1
  have P2 := planeD_at (gL := gL) (i := i) G A2 fD (q := 0) o2.1 o2.2 F2 rfl rfl T.aD1
  have P3 := planeM_at (gL := gL) (i := i) G A3 f3 (q := 1) o3.1 o3.2 F3 rfl rfl T.aM2
  have P4 := planeD_at (gL := gL) (i := i) G A4 f4 (q := 1) o4.1 o4.2 F4 rfl rfl T.aD2
  have k1 : EndsIn (zk.getD c1.call #[]) zx := by rw [o3.1]; exact endsIn_of (G.keys 1)
  have k2 : EndsIn (zk.getD c2.call #[]) zx := by rw [o4.1]; exact endsIn_of (G.keys 1)
  have TM := tieM_of G.fit L N Z A3.cut U1 k1 bM
  have TD := tieD_of G.fit L N Z A4.cut U2 k2 bD
  have pw1 : (unitsOf pM pD kM kD tM tD).kM.pw = (remBack c1).pw := by
    show pwBack kM.pw = pwBack c1.pw
    rw [U1.pw]
  have pw2 : (unitsOf pM pD kM kD tM tD).kD.pw = (remBack c2).pw := by
    show pwBack kD.pw = pwBack c2.pw
    rw [U2.pw]
  obtain ⟨a5, b5⟩ := F5 _ (keyPt_of G.fit G.look (G.keys 2))
  obtain ⟨a6, b6⟩ := F6 _ (keyPt_of G.fit G.look (G.keys 2))
  obtain ⟨a7, b7⟩ := F7 _ (keyPt_of G.fit G.look (G.keys 3))
  exact
    { m1 := P1, m1n := nM, d1 := P2, d1n := nD, m2 := P3, m2n := U1.np, m2s := U1.s0, d2 := P4,
      d2n := U2.np, d2s := U2.s0,
      msM := ⟨by rw [pw1]; exact P3.pairs, by rw [pw1]; exact P3.w, TM.sg, TM.si, TM.g, TM.i, T.mM⟩,
      msMI := TM.wI,
      msD := ⟨by rw [pw2]; exact P4.pairs, by rw [pw2]; exact P4.w, TD.sg, TD.si, TD.g, TD.i, T.mD⟩,
      msDI := TD.wI,
      wl := ⟨by show PiecesAll S (pwBack i.p.d.pwW); rw [w5]; exact a5,
        by show ∀ b < S.NP, ρ.val ((pwBack i.p.d.pwW).getD b default).wp = _; rw [w5]; exact b5,
        T5.sgW, T5.siW, T5.scW, T5.gW, T5.iW, T5.nW, T.oW⟩,
      wlT := T.hW,
      wh := ⟨by show PiecesAll S (pwBack i.p.d.pwH); rw [h5]; exact a7,
        by show ∀ b < S.NP, ρ.val ((pwBack i.p.d.pwH).getD b default).wp = _; rw [h5]; exact b7,
        T5.sgH, T5.siH, T5.scH, T5.gH, T5.iH, T5.nH, T.oH⟩,
      ixP := by show PiecesAll S (pwBack i.p.d.pwX); rw [x5]; exact a6,
      ixW := by
        show ∀ b < S.NP, ρ.val ((pwBack i.p.d.pwX).getD b default).wp = _
        rw [x5]
        exact b6,
      ixZg := T5.sgX, ixZi := T5.siX, ixG := T5.gX, ixI := T5.iX, ixT := T.hX }

end K5Law

#print axioms K5Law.linPub_of
