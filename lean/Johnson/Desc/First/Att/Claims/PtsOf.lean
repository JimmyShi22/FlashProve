-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PtsOf.lean: kind K5: the record PtsAre that port_cl takes
(Johnson/Desc/First/Att/Claims/PortAll.lean), paid: the verifier's points and weights at the
lookup's end point are the library's, at a record of the kind's own: h := oldOf S gL i
(Johnson/Desc/First/Att/Claims/Any.lean), the six sixPl …
(Johnson/Desc/First/Att/Claims/Place.lean).

Main names:
  `pw_back`: the pieces of a unit of the place, carried back, are the planner's pieces of the list
    (pieces_old, Johnson/Desc/First/Att/Claims/PtsBridge.lean).
  `planePts_of`: a plane claim's PlanePts: its point is the family's inner point (pc_size, pc_pt,
    Johnson/Desc/First/Att/Claims/PointsTieU.lean); its pieces are the pairs, with the library's
    weights (FamAt, Johnson/Desc/First/Att/Claims/PiecesTie.lean).
  `callAt_of`, `place_wl`, `points_pw`, `single_call`.
  `pts_core`: PlanePts at the four plane claims (families m1, d1, m2, d2), MaxIs at the two units,
    DivIs: at D := dimOf S, C := callsOf fs, z := p.z. `pts_are`: PtsAre at parameters P with P.D =
    dimOf S, P.C = callsOf fs and zT u = p.z.
Premises: shapeHid lid cf = ok (S, fs); UsualCalls cf and CallsFit S fs
(Johnson/Road/Lane5AttLaid.lean, Lane5CallsOf.lean: two public tests); LookAll ρ fs zx zy p and
KeyIs at the four calls' key points (Johnson/Desc/First/Att/Claims/LookKeys.lean: the library's z is
the lookup's end point, read; each call's key point is the lookup's cut of it); PlaceIs; the return
of pointsOf; the return of "first" (for the lawful heads: in_high_fe,
Johnson/Desc/First/Att/Claims/InHigh.lean). None of the tests is asked by the verifier; LookAll and
KeyIs are not shown in this file or in what it imports.
Used: Johnson/Desc/First/Att/Claims/PointsTie.lean (tie5_of, cut5_of), PointsCut.lean (cutU_of),
PointsTieU.lean (tieM_of, tieD_of), PiecesTie.lean (seven_of_hid), LookKeys.lean; norm_of_hid,
sizes_of_hid (Johnson/Road/Rows/AttReadLong.lean). Of OnBytes and Johnson/Road no routine that runs
in a context is named, and no theorem on such a routine's return; the runs spoken of are the kind's
own (Johnson/Desc/First/Att/RunsP.lean).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.PointsTieU
import Johnson.Desc.First.Att.Claims.PiecesTie
import Johnson.Desc.First.Att.Claims.LookKeys
import Johnson.Desc.First.Att.Claims.PtsBridge
import Johnson.Desc.First.Att.Claims.Place
import Johnson.Desc.First.Att.Claims.InHigh

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.Road.L5 (callAt)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo CallG Keys UnitG ScoreP RemP Pts geoOf callOf keysOf)
open Inst.Model.AttSeg (Pub Fam Reg)
open Cb.Pv.Att.End (IsPlane)

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {S : Attention.Shape} {fs : Model.Forest.Shape}
  {zx : Array E} {p : Pub Kf} {zk : Array (Array E)} {gL : Forest.Heard} {i : P.Runs.In}

/-- The pieces of a unit of the place, carried back, are the planner's pieces of the list. -/
theorem pw_back (q : ℕ) (c : ACall) (s : Attention.Seg) (key : Array E) :
    pwBack (P.piecesOf ((geoOf S).unitAt q (callOf c) (keysOf s)) key) = pieces c key s := by
  rw [pieces_old, pwBack_of]

/-- **A plane claim's public facts**: its point is the family's inner point; its pieces are the pairs, with the library's weights. -/
theorem planePts_of (hF : L5.CallsFit S fs) (L : Look ρ fs zx p) {q : Fin 4} {c : ACall}
    (hc : callAt S q.val = c) {s : Attention.Seg} {fam : Fam} (FA : FamAt ρ S fs p q s fam)
    (KP : KeyPt ρ fs (zk.getD q.val #[]) q p) (hk : EndsIn (zk.getD q.val #[]) zx) (hpl : IsPlane fam)
    {pc : RemP} (hcall : pc.call = q.val)
    (hz : pc.z = P.inner ((geoOf S).unitAt q.val (callOf c) (keysOf s)) (zk.getD q.val #[]))
    (hw : pc.pw = P.piecesOf ((geoOf S).unitAt q.val (callOf c) (keysOf s)) (zk.getD q.val #[]))
    (hbits : (geoOf S).keyBits (keysOf s) = (geoOf S).keyBits (if pc.isD then .rd else .rm))
    (hb : (geoOf S).keyBits (if pc.isD then .rd else .rm) = fam.l (L5.dimOf S))
    (hreg : fam.reg = if pc.isD then Reg.D else Reg.M)
    (hnb : (if pc.isD then S.nD else S.nM) = fam.l (L5.dimOf S)) :
    PlanePts ρ (oldOf S gL i) (L5.dimOf S) (L5.callsOf fs) p.z fam (remBack pc) := by
  have H : PlaneCut (geoOf S) zk pc :=
    ⟨(geoOf S).unitAt q.val (callOf c) (keysOf s), hbits, by rw [hcall]; exact hz, by rw [hcall]; exact hw⟩
  have hk' : EndsIn (zk.getD pc.call #[]) zx := by rw [hcall]; exact hk
  have ew : (remBack pc).pw = pieces (callAt S q.val) (zk.getD q.val #[]) s := by
    show pwBack pc.pw = _
    rw [hw, pw_back, hc]
  obtain ⟨f1, f2⟩ := FA _ KP
  refine ⟨hpl, by rw [ew]; exact f1, hreg, hnb, pc_size hF L H hk' fam hb,
    fun j hj => pc_pt hF L H hk' fam hb (by omega), by rw [ew]; exact f2⟩

variable {c0 c1 c2 c3 : ACall}

theorem callAt_of (Pl : PlaceIs S c0 c1 c2 c3) :
    callAt S 0 = c0 ∧ callAt S 1 = c1 ∧ callAt S 2 = c2 ∧ callAt S 3 = c3 := by
  have e : ∀ n, callAt S n = (S.calls.toList[n]?).getD default := by
    intro n
    unfold callAt
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_toList]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [e, Pl.calls] <;> rfl

/-- The units of the lists wl and ix lie in call 2. -/
theorem place_wl (Pl : PlaceIs S c0 c1 c2 c3) :
    (geoOf S).single .wl = some ((geoOf S).unitAt 2 (callOf c2) .wl) ∧
      (geoOf S).single .ix = some ((geoOf S).unitAt 2 (callOf c2) .ix) := by
  have e2 : (geoOf S).calls[2]? = some (callOf c2) := by
    have : (geoOf S).calls.toList = [callOf c0, callOf c1, callOf c2, callOf c3] := by
      show (S.calls.map callOf).toList = _
      rw [Array.toList_map, Pl.calls]
      rfl
    rw [← Array.getElem?_toList, this]
    rfl
  constructor <;> unfold P.Geo.single P.Geo.lastHolding <;> rw [place_zip Pl] <;>
    simp [callOf, P.CallG.holds, keysOf, Pl.g0, Pl.g1, Pl.g2, Pl.g3, e2]

/-- What pointsOf lays as the three single units' pieces. -/
theorem points_pw {g : Geo} {h : P.Heard} {L : P.Left} {q : Pts} (hp : P.pointsOf g zk h L = some q) :
    ∃ uW uX uH, g.single .wl = some uW ∧ g.single .ix = some uX ∧ g.single .wh = some uH ∧
      q.d.pwW = P.piecesOf uW (zk.getD uW.call #[]) ∧ q.d.pwX = P.piecesOf uX (zk.getD uX.call #[]) ∧
      q.d.pwH = P.piecesOf uH (zk.getD uH.call #[]) := by
  unfold P.pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, _, _, _, a, _, uW, hW, uX, hX, uH, hH, _, _, _, _, e⟩ := hp
  subst e
  exact ⟨uW, uX, uH, hW, hX, hH, rfl, rfl, rfl⟩

open Cb.Pv.Att (OwnPar)
open Cb.Pv.Att.End (zT)
open VerifiableInference.Desc.First.Att.P.Runs (JoinsP)

/-- The unit of a list that one call alone serves lies in a call of the place. -/
theorem single_call {g : Geo} {k : Keys} {u : UnitG} (h : g.single k = some u) : u.call < g.calls.size := by
  unfold P.Geo.single at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨q, _, c, hc, rfl⟩ := h
  show q < _
  rcases Nat.lt_or_ge q g.calls.size with h' | h'
  · exact h'
  · rw [Array.getElem?_eq_none h'] at hc; cases hc

/-- **PtsAre, at the library's letters**: the seven records at D := dimOf S, C := callsOf fs, z := p.z. -/
theorem pts_core {lid : ℕ} {cf : Attention.Cfg} {zy : Array E}
    (hid : shapeHid lid cf = Except.ok (S, fs)) (U : L5.UsualCalls cf) (hF : L5.CallsFit S fs)
    (A : LookAll ρ fs zx zy p) (hK : ∀ q : Fin 4, KeyIs fs zx zy (zk.getD q.val #[]) q)
    (Pl : PlaceIs S c0 c1 c2 c3) (hg : i.g = geoOf S) {hh : P.Heard} {L' : P.Left}
    (hP : P.pointsOf i.g zk hh L' = some i.p) {a1 a2 : ℕ} {k1 k2 : ScoreP}
    (hk1 : i.p.scores[0]? = some k1) (hk2 : i.p.scores[1]? = some k2)
    {K : ℕ} {x : List Aff × JoinsP} (h1 : P.Runs.firstRun (inOld (oldOf S gL i)) K = some x) :
    PlanePts ρ (oldOf S gL i) (L5.dimOf S) (L5.callsOf fs) p.z .m1 (sixPl i zk c0 c1 a1 a2 k1 k2).pM ∧
    PlanePts ρ (oldOf S gL i) (L5.dimOf S) (L5.callsOf fs) p.z .d1 (sixPl i zk c0 c1 a1 a2 k1 k2).pD ∧
    PlanePts ρ (oldOf S gL i) (L5.dimOf S) (L5.callsOf fs) p.z .m2 (sixPl i zk c0 c1 a1 a2 k1 k2).cM ∧
    PlanePts ρ (oldOf S gL i) (L5.dimOf S) (L5.callsOf fs) p.z .d2 (sixPl i zk c0 c1 a1 a2 k1 k2).cD ∧
    MaxIs ρ (oldOf S gL i) (L5.dimOf S) (L5.callsOf fs) p.z .m2
      (Inst.Model.AttSeg.zg (L5.dimOf S) (L5.callsOf fs) p.z) (sixPl i zk c0 c1 a1 a2 k1 k2).kM ∧
    MaxIs ρ (oldOf S gL i) (L5.dimOf S) (L5.callsOf fs) p.z .d2
      (Inst.Model.AttSeg.zgD (L5.dimOf S) (L5.callsOf fs) p.z) (sixPl i zk c0 c1 a1 a2 k1 k2).kD ∧
    DivIs ρ (oldOf S gL i) (L5.dimOf S) (L5.callsOf fs) p.z := by
  have N := norm_of_hid hid
  have Z := sizes_of_hid hid
  have L := look_of A
  have hE : ∀ q : Fin 4, EndsIn (zk.getD q.val #[]) zx := fun q => endsIn_of (hK q)
  have KP : ∀ q : Fin 4, KeyPt ρ fs (zk.getD q.val #[]) q p := fun q => keyPt_of hF A (hK q)
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := seven_of_hid ρ hid U p
  obtain ⟨q0, q1, q2, q3⟩ := callAt_of Pl
  rw [hg] at hP
  have Pn := planes_are hP
  have PA := points_are hP
  have CU := cutU_of hP
  have hgs := place_scores Pl
  have nH : hh.scores.size = 2 := by rw [← PA.nH, hgs]; rfl
  have eo1 : hh.scores[0]? = some hh.scores[0] := Array.getElem?_eq_getElem (by omega)
  have eo2 : hh.scores[1]? = some hh.scores[1] := Array.getElem?_eq_getElem (by omega)
  obtain ⟨k1', s1, _, d1, z1, b1, w1', _⟩ := Pn.unit 0 _ _ (by rw [hgs]; rfl) eo1
  obtain ⟨k2', s2, _, d2, z2, b2, w2', _⟩ := Pn.unit 1 _ _ (by rw [hgs]; rfl) eo2
  rw [hk1] at s1
  rw [hk2] at s2
  have e1 : k1' = k1 := (Option.some.inj s1).symm
  have e2 : k2' = k2 := (Option.some.inj s2).symm
  subst e1 e2
  have m1 : k1' ∈ i.p.scores.toList := List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hk1)
  have m2 : k2' ∈ i.p.scores.toList := List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact hk2)
  obtain ⟨pc1, g1, U1⟩ := CU.units k1' m1
  obtain ⟨pc2, g2, U2⟩ := CU.units k2' m2
  have H1 : PlaneCut (geoOf S) zk pc1 :=
    (CU.planes pc1 (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact g1))).cut
  have H2 : PlaneCut (geoOf S) zk pc2 :=
    (CU.planes pc2 (List.mem_of_getElem? (by rw [Array.getElem?_toList]; exact g2))).cut
  rw [d1] at g1
  rw [d2] at g2
  have c1e : pc1.call = 1 := by rw [← Option.some.inj g1]; rfl
  have c2e : pc2.call = 1 := by rw [← Option.some.inj g2]; rfl
  have T1 := tieM_of (ρ := ρ) (p := p) hF L N Z H1 U1 (by rw [c1e]; exact hE 1) (by rw [b1]; rfl)
  have T2 := tieD_of (ρ := ρ) (p := p) hF L N Z H2 U2 (by rw [c2e]; exact hE 1) (by rw [b2]; rfl)
  have T5 := tie5_of (ρ := ρ) (p := p) hF L N.lt (zk := zk)
    (fun u ⟨k, hu⟩ => by
      have h4 : u.call < 4 := by
        have := single_call hu
        have e4 : (geoOf S).calls.size = 4 := by
          show (S.calls.map callOf).size = 4
          rw [Array.size_map, ← Array.length_toList, Pl.calls]
          rfl
        omega
      exact hE ⟨u.call, h4⟩) (cut5_of hP)
  obtain ⟨uW, uX, uH, hW, hX, hH, pwW, pwX, pwH⟩ := points_pw hP
  rw [(place_wl Pl).1] at hW
  rw [(place_wl Pl).2] at hX
  rw [place_wh Pl] at hH
  rw [← Option.some.inj hW] at pwW
  rw [← Option.some.inj hX] at pwX
  rw [← Option.some.inj hH] at pwH
  have eW : (oldOf S gL i).d.pwW = pieces (callAt S 2) (zk.getD 2 #[]) .wl := by
    show pwBack i.p.d.pwW = _
    rw [pwW, q2]
    exact pw_back 2 c2 .wl _
  have eX : (oldOf S gL i).d.pwX = pieces (callAt S 2) (zk.getD 2 #[]) .ix := by
    show pwBack i.p.d.pwX = _
    rw [pwX, q2]
    exact pw_back 2 c2 .ix _
  have eH : (oldOf S gL i).d.pwH = pieces (callAt S 3) (zk.getD 3 #[]) .wh := by
    show pwBack i.p.d.pwH = _
    rw [pwH, q3]
    exact pw_back 3 c3 .wh _
  have eM : (scoreBack k1').pw = pieces (callAt S 1) (zk.getD 1 #[]) .fm := by
    show pwBack k1'.pw = _
    rw [w1', q1]
    exact pw_back 1 c1 .fm _
  have eD : (scoreBack k2').pw = pieces (callAt S 1) (zk.getD 1 #[]) .fd := by
    show pwBack k2'.pw = _
    rw [w2', q1]
    exact pw_back 1 c1 .fd _
  have pW : PiecesAll S (oldOf S gL i).d.pwW := by rw [eW]; exact (f5 _ (KP 2)).1
  have pH : PiecesAll S (oldOf S gL i).d.pwH := by rw [eH]; exact (f7 _ (KP 3)).1
  unfold sixPl sixAt
  dsimp only
  rw [hg]
  refine ⟨?_, ?_, ?_, ?_, ⟨?_, ?_, T1.g, ?_⟩, ⟨?_, ?_, T2.g, ?_⟩, ?_⟩
  · exact planePts_of hF L (q := 0) q0 (s := .rm) f1 (KP 0) (hE 0) trivial rfl rfl rfl rfl (bitsM N) rfl N.nM
  · exact planePts_of hF L (q := 0) q0 (s := .rd) f2 (KP 0) (hE 0) trivial rfl rfl rfl rfl (bitsD N) rfl N.nD
  · exact planePts_of hF L (q := 1) q1 (s := .fm) f3 (KP 1) (hE 1) trivial rfl rfl rfl rfl (bitsM N) rfl N.nM
  · exact planePts_of hF L (q := 1) q1 (s := .fd) f4 (KP 1) (hE 1) trivial rfl rfl rfl rfl (bitsD N) rfl N.nD
  · rw [eM]; exact (f3 _ (KP 1)).1
  · exact Nat.le_of_eq T1.sg.symm
  · rw [eM]; exact (f3 _ (KP 1)).2
  · rw [eD]; exact (f4 _ (KP 1)).1
  · exact Nat.le_of_eq T2.sg.symm
  · rw [eD]; exact (f4 _ (KP 1)).2
  · exact ⟨pW, by rw [eX]; exact (f6 _ (KP 2)).1, pH, by rw [eW]; exact (f5 _ (KP 2)).2,
      by rw [eX]; exact (f6 _ (KP 2)).2, by rw [eH]; exact (f7 _ (KP 3)).2,
      Nat.le_of_eq T5.sgW.symm, Nat.le_of_eq T5.sgX.symm, Nat.le_of_eq T5.sgH.symm, T5.scW, T5.scH,
      T5.gW, T5.gX, T5.gH, T5.nW, T5.nH, in_high_fe (oldOf S gL i) h1 Z.G pW pH⟩

/-- **PtsAre, paid**, at parameters whose sizes, calls and end point are these. -/
theorem pts_are [Fintype Kf] {M X : Type} {Pp : OwnPar Kf M X} {u : Pp.Run} {lid : ℕ} {cf : Attention.Cfg}
    {zy : Array E} (hid : shapeHid lid cf = Except.ok (S, fs)) (U : L5.UsualCalls cf)
    (hF : L5.CallsFit S fs) (A : LookAll ρ fs zx zy p)
    (hK : ∀ q : Fin 4, KeyIs fs zx zy (zk.getD q.val #[]) q) (Pl : PlaceIs S c0 c1 c2 c3)
    (hg : i.g = geoOf S) {hh : P.Heard} {L' : P.Left} (hP : P.pointsOf i.g zk hh L' = some i.p)
    {a1 a2 : ℕ} {k1 k2 : ScoreP} (hk1 : i.p.scores[0]? = some k1) (hk2 : i.p.scores[1]? = some k2)
    {K : ℕ} {x : List Aff × JoinsP} (h1 : P.Runs.firstRun (inOld (oldOf S gL i)) K = some x)
    (hD : Pp.D = L5.dimOf S) (hC : Pp.C = L5.callsOf fs) (hz : zT u = p.z) :
    PtsAre ρ (oldOf S gL i) Pp u (sixPl i zk c0 c1 a1 a2 k1 k2) := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := pts_core (gL := gL) (a1 := a1) (a2 := a2) hid U hF A hK Pl hg hP
    hk1 hk2 h1
  exact ⟨by rw [hD, hC, hz]; exact t1, by rw [hD, hC, hz]; exact t2, by rw [hD, hC, hz]; exact t3,
    by rw [hD, hC, hz]; exact t4, by rw [hD, hC, hz]; exact t5, by rw [hD, hC, hz]; exact t6,
    by rw [hD, hC, hz]; exact t7⟩

end K5Law
