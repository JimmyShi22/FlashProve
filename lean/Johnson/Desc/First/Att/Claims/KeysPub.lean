-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/KeysPub.lean: kind K5: the last joint, first part: which call a unit
of the record lies in; its pieces in the letters of OnBytes/Model; the records PlaneM and PlaneD
(Johnson/Desc/First/Att/Claims/KeysWorth.lean) at a plane claim that pointsOf made.

Main names:
  `call_at`, `kr_is_0`, `kfd_is_1`: a call of the place made of a shape with the four usual calls is
    callOf (callAt S q), q < 4; the remainder-table call is call 0, the softmax-table call call 1.
  `plane_old`: a plane claim of the record lies in call 0 (three planes) or call 1 (five), and its
    pieces are Attention.pieces of that call's list rm | rd | fm | fd.
  `Cut5w`, `cut5w_of`: what pointsOf lays into the division's pieces, with its guard "as many pieces
    as pairs".
  `single_old`: the unit of a list that one call alone serves lies in the one call whose pieces hold
    the list, where it has a piece at all.
  `Ground`: the planner's shape at the usual call list; CallsFit; each call's key point is the
    lookup's cut of its end point; the library's z is that end point, read.
  `planeM_at`, `planeD_at`: all of PlaneM | PlaneD but the table clause.
Used: FourCalls, four_of_hid (Johnson/Road/Lane5AttLaid.lean); calls_zip (Claim3b.lean); pieces_old
(PtsBridge.lean); pwBack_of (Any.lean); PointsCut.lean, PointsTieU.lean, PiecesTie.lean,
LookKeys.lean.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.KeysWorth
import Johnson.Desc.First.Att.Claims.PointsTieU
import Johnson.Desc.First.Att.Claims.LookKeys
import Johnson.Desc.First.Att.Claims.PtsBridge

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.Road.L5 (callAt FourCalls UsualCalls)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Geo Pts ScoreP RemP UnitG CallG geoOf callOf keysOf tabOf
  w1Of)
open Inst.Model.AttSeg (Pub Fam wp inn)

variable {Kf : Type} [Field Kf] {cf : Cfg} {S : Attention.Shape}

/-- A call of the place made of a shape with four calls. -/
theorem call_at (Fo : FourCalls cf S) {c' : CallG} {q : ℕ}
    (h : (c', q) ∈ (geoOf S).calls.toList.zipIdx) : q < 4 ∧ c' = callOf (callAt S q) := by
  rw [calls_zip] at h
  obtain ⟨x, hx, e⟩ := List.mem_map.1 h
  obtain ⟨c, q'⟩ := x
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, rfl⟩ := e
  rw [List.mem_zipIdx_iff_getElem?] at hx
  have hx' : S.calls[q']? = some c := by simpa using hx
  have hlt : q' < S.calls.size := by
    by_contra hc
    rw [Array.getElem?_eq_none (by omega)] at hx'
    cases hx'
  refine ⟨by rw [← Fo.size]; exact hlt, ?_⟩
  unfold callAt
  rw [Array.getD_eq_getD_getElem?, hx']
  rfl

theorem kr_is_0 (Fo : FourCalls cf S) {q : ℕ} (hq : q < 4)
    (h : ((callOf (callAt S q)).tab == .kr) = true) : q = 0 := by
  obtain ⟨k0, k1, k2, k3⟩ := Fo.kind
  have h' : (tabOf (callAt S q).kind == P.Tab.kr) = true := h
  interval_cases q
  · rfl
  · rw [k1] at h'; cases h'
  · rw [k2] at h'; cases h'
  · rw [k3] at h'; cases h'

theorem kfd_is_1 (Fo : FourCalls cf S) {q : ℕ} (hq : q < 4)
    (h : ((callOf (callAt S q)).tab == .kfd) = true) : q = 1 := by
  obtain ⟨k0, k1, k2, k3⟩ := Fo.kind
  have h' : (tabOf (callAt S q).kind == P.Tab.kfd) = true := h
  interval_cases q
  · rw [k0] at h'; cases h'
  · rfl
  · rw [k2] at h'; cases h'
  · rw [k3] at h'; cases h'

/-- **A plane claim of the record, in the letters of OnBytes/Model**: its call's number q (0 with
three planes, 1 with five), and its pieces are Attention.pieces of that call's list. -/
theorem plane_old (Fo : FourCalls cf S) {zk : Array (Array E)} {pc : RemP}
    (H : PlaneAt (geoOf S) zk pc) :
    (pc.np = 3 ∧ pc.call = 0 ∧ (remBack pc).pw =
        pieces (callAt S 0) (zk.getD 0 #[]) (if pc.isD then .rd else .rm)) ∨
      (pc.np = 5 ∧ pc.call = 1 ∧ (remBack pc).pw =
        pieces (callAt S 1) (zk.getD 1 #[]) (if pc.isD then .fd else .fm)) := by
  obtain ⟨c, k, hc, hk, _, ew⟩ := H
  obtain ⟨hq, rfl⟩ := call_at Fo hc
  rcases hk with ⟨ht, rfl, hn⟩ | ⟨ht, rfl, hn⟩
  · have h0 := kr_is_0 Fo hq ht
    refine .inl ⟨hn, h0, ?_⟩
    show pwBack pc.pw = _
    rw [ew, h0]
    have e : (if pc.isD = true then P.Keys.rd else P.Keys.rm) =
        keysOf (if pc.isD then Attention.Seg.rd else Attention.Seg.rm) := by cases pc.isD <;> rfl
    rw [e, pieces_old, pwBack_of]
  · have h1 := kfd_is_1 Fo hq ht
    refine .inr ⟨hn, h1, ?_⟩
    show pwBack pc.pw = _
    rw [ew, h1]
    have e : (if pc.isD = true then P.Keys.fd else P.Keys.fm) =
        keysOf (if pc.isD then Attention.Seg.fd else Attention.Seg.fm) := by cases pc.isD <;> rfl
    rw [e, pieces_old, pwBack_of]

/-! ## The three lists that one call alone serves -/

/-- What pointsOf lays into the division's pieces. -/
structure Cut5w (g : Geo) (zk : Array (Array E)) (p : Pts) : Prop where
  at' : ∃ uW uX uH : UnitG, g.single .wl = some uW ∧ g.single .ix = some uX ∧
    g.single .wh = some uH ∧ p.d.pwW = P.piecesOf uW (zk.getD uW.call #[]) ∧
    p.d.pwX = P.piecesOf uX (zk.getD uX.call #[]) ∧ p.d.pwH = P.piecesOf uH (zk.getD uH.call #[]) ∧
    p.d.pwW.size = g.NP ∧ p.d.pwX.size = g.NP ∧ p.d.pwH.size = g.NP

theorem cut5w_of {g : Geo} {zk : Array (Array E)} {h : P.Heard} {L : P.Left} {p : Pts}
    (hp : P.pointsOf g zk h L = some p) : Cut5w g zk p := by
  unfold P.pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, _, _, hn, a, hf, uW, hW, uX, hX, uH, hH, _, hs, _, hz, e⟩ := hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  subst e
  exact ⟨uW, uX, uH, hW, hX, hH, rfl, rfl, rfl, hs.1.1, hs.1.2, hs.2⟩

theorem single_at {g : Geo} {k : P.Keys} {u : UnitG} (h : g.single k = some u) :
    ∃ q c, g.calls[q]? = some c ∧ u = g.unitAt q c k := by
  unfold P.Geo.single at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨q, _, c, hc, rfl⟩ := h
  exact ⟨q, c, hc, rfl⟩

/-- A call without a piece of the list has no piece of it. -/
theorem pieces_none {c : ACall} {s : Attention.Seg}
    (h : ∀ pc ∈ c.pcs.toList, (pc.seg == s) = false) (zk : Array E) : (pieces c zk s).size = 0 := by
  unfold pieces
  dsimp only
  rw [filterMap_none _ _ (fun pc hpc => by rw [h pc hpc]; rfl), List.size_toArray,
    List.length_mergeSort]
  rfl

theorem mem_two {s s1 s2 : Attention.Seg} (h1 : (s1 == s) = false) (h2 : (s2 == s) = false)
    {l : List Attention.Piece} {HA c1 b1 n1 c2 b2 n2 : ℕ}
    (hl : l = L5.famAt s1 HA c1 b1 n1 ++ L5.famAt s2 HA c2 b2 n2) :
    ∀ pc ∈ l, (pc.seg == s) = false := by
  intro pc hpc
  rw [hl] at hpc
  rcases List.mem_append.1 hpc with h | h
  · exact fam_other h1 _ _ _ _ pc h
  · exact fam_other h2 _ _ _ _ pc h

/-- **The unit of a list that one call alone serves, in the letters of OnBytes/Model**, where it has
a piece: q0: the one call whose pieces hold the list. -/
theorem single_old (Fo : FourCalls cf S) {s : Attention.Seg} {q0 : ℕ}
    (hno : ∀ q < 4, q ≠ q0 → ∀ pc ∈ (callAt S q).pcs.toList, (pc.seg == s) = false)
    {u : UnitG} (hu : (geoOf S).single (keysOf s) = some u) (zk : Array (Array E))
    (hpos : 0 < (P.piecesOf u (zk.getD u.call #[])).size) :
    u.call = q0 ∧ pwBack (P.piecesOf u (zk.getD u.call #[])) =
      pieces (callAt S q0) (zk.getD q0 #[]) s := by
  obtain ⟨q, c, hc, rfl⟩ := single_at hu
  have hm : (c, q) ∈ (geoOf S).calls.toList.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simpa using hc
  obtain ⟨hq, rfl⟩ := call_at Fo hm
  have e : P.piecesOf ((geoOf S).unitAt q (callOf (callAt S q)) (keysOf s)) (zk.getD q #[]) =
      w1Of (pieces (callAt S q) (zk.getD q #[]) s) := pieces_old S q _ s _
  have hq0 : q = q0 := by
    by_contra hne
    have h0 := pieces_none (hno q hq hne) (zk.getD q #[])
    have h1 : 0 < (w1Of (pieces (callAt S q) (zk.getD q #[]) s)).size := by
      rw [← e]
      exact hpos
    unfold w1Of at h1
    rw [Array.size_map, h0] at h1
    omega
  subst hq0
  refine ⟨rfl, ?_⟩
  show pwBack (P.piecesOf ((geoOf S).unitAt q (callOf (callAt S q)) (keysOf s)) (zk.getD q #[])) = _
  rw [e, pwBack_of]

/-! ## The ground, and the records -/

/-- **The ground**: the shape is the planner's at the usual call list; the lookup's numbers fit;
each call's key point is the lookup's cut of its end point; the library's z is that end point,
read. -/
structure Ground (ρ : Reading Kf) (lid : ℕ) (cf : Cfg) (S : Attention.Shape)
    (fs : Model.Forest.Shape) (zx zy : Array E) (zk : Array (Array E)) (p : Pub Kf) : Prop where
  hid : shapeHid lid cf = Except.ok (S, fs)
  usual : UsualCalls cf
  fit : L5.CallsFit S fs
  look : LookAll ρ fs zx zy p
  keys : ∀ c : Fin 4, KeyIs fs zx zy (zk.getD c.val #[]) c

variable {ρ : Reading Kf} {lid : ℕ} {fs : Model.Forest.Shape} {zx zy : Array E}
  {zk : Array (Array E)} {p : Pub Kf} {gL : Forest.Heard} {i : P.Runs.In}

/-- A plane claim below the diagonal: all of PlaneM but the table. -/
theorem planeM_at (G : Ground ρ lid cf S fs zx zy zk p) {pc : RemP}
    (H : PlaneAt (geoOf S) zk pc) (hD : pc.isD = false) {q : Fin 4} {s : Attention.Seg} {f : Fam}
    (hq : pc.call = q.val) (hw : (remBack pc).pw = pieces (callAt S q.val) (zk.getD q.val #[]) s)
    (F : FamAt ρ S fs p q s f) (hr : f.reg = .M) (hl : f.l (L5.dimOf S) = (L5.dimOf S).lM)
    (tab : AsAt (oldOf S gL i) (oldOf S gL i).t.tA (lastN pc.z S.cf.lmS)) :
    PlaneM ρ (oldOf S gL i) (L5.callsOf fs) p (remBack pc) f := by
  have N := norm_of_hid G.hid
  have L := look_of G.look
  have hk : EndsIn (zk.getD pc.call #[]) zx := by rw [hq]; exact endsIn_of (G.keys q)
  have hb : (geoOf S).keyBits (if pc.isD then .rd else .rm) = f.l (L5.dimOf S) := by
    rw [hD, hl]
    exact bitsM N
  have hnM : f.l (L5.dimOf S) = S.nM := by rw [hl]; exact N.nM.symm
  obtain ⟨h1, h2⟩ := F _ (keyPt_of G.fit G.look (G.keys q))
  refine ⟨hD, hr, hnM, ?_, ?_, ?_, ?_, tab⟩
  · rw [hw]; exact h1
  · rw [hw]; exact h2
  · exact (pc_size G.fit L H.cut hk f hb).trans hnM
  · intro j hj
    exact pc_pt G.fit L H.cut hk f hb (by rw [hnM]; exact hj)

/-- A plane claim on the diagonal: all of PlaneD but the table. -/
theorem planeD_at (G : Ground ρ lid cf S fs zx zy zk p) {pc : RemP}
    (H : PlaneAt (geoOf S) zk pc) (hD : pc.isD = true) {q : Fin 4} {s : Attention.Seg} {f : Fam}
    (hq : pc.call = q.val) (hw : (remBack pc).pw = pieces (callAt S q.val) (zk.getD q.val #[]) s)
    (F : FamAt ρ S fs p q s f) (hr : f.reg = .D) (hl : f.l (L5.dimOf S) = (L5.dimOf S).lD)
    (tab : AsAt (oldOf S gL i) (oldOf S gL i).t.tA (lastN pc.z S.cf.lmS)) :
    PlaneD ρ (oldOf S gL i) (L5.callsOf fs) p (remBack pc) f := by
  have N := norm_of_hid G.hid
  have L := look_of G.look
  have hk : EndsIn (zk.getD pc.call #[]) zx := by rw [hq]; exact endsIn_of (G.keys q)
  have hb : (geoOf S).keyBits (if pc.isD then .rd else .rm) = f.l (L5.dimOf S) := by
    rw [hD, hl]
    exact bitsD N
  have hnD : f.l (L5.dimOf S) = S.nD := by rw [hl]; exact N.nD.symm
  obtain ⟨h1, h2⟩ := F _ (keyPt_of G.fit G.look (G.keys q))
  refine ⟨hD, hr, hnD, ?_, ?_, ?_, ?_, tab⟩
  · rw [hw]; exact h1
  · rw [hw]; exact h2
  · exact (pc_size G.fit L H.cut hk f hb).trans hnD
  · intro j hj
    exact pc_pt G.fit L H.cut hk f hb (by rw [hnD]; exact hj)

end K5Law

#print axioms K5Law.planeM_at
#print axioms K5Law.planeD_at
#print axioms K5Law.plane_old
#print axioms K5Law.single_old
