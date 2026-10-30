-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/KeysIn.lean: kind K5: where "first" returns, the indices that the
linear claims on the key forms' named scalars read lie in their tables, and the heads' features are
lawful: the premises that Johnson/Desc/First/Att/Claims/KeysLin.lean adds to those of
Johnson/Road/Rows, drawn out of the run's return. It does for these claims what
Johnson/Desc/First/Att/Claims/InRunAll.lean does for the end values.

Main names:
  `rc_lessPieces`: where lessPieces returns, what each piece's form asks holds of every piece.
  `PlaneIn h pc`, `MaxIn h k tM`, `HighIn h pw zc`, `DenIn h`, `BitIn h`: the premises at a plane
    claim, at a unit's row maxima, at a segment that reads the high parts of the remainders, at the
    denominator, at the index's bits: for every piece of the list.
  `in_planeKR`, `in_unitLin`, `in_five`: "first" returns ⇒ these, at a plane claim of a visited
    remainder-table call; at a visited softmax-table unit with its plane claim; at claim 5.
Each speaks of the pieces b < pw.size. Where the list has a piece for each pair (PiecesAll), that is
b < NP, the form in which LinPub (Johnson/Desc/First/Att/Claims/KeysWorth.lean) asks them.
Used: RC and its laws (PointsRows.lean, InRun.lean), rc_plane, rc_readMaximum, rc_readDenominator,
rc_readIndexBit, rc_readHead, InLongG (InRun.lean); calls_zip, tab_eq, planes_inOld (Claim3b.lean);
scores_zip, scoreT_inOld (Claim4.lean); getD_lam, getD_a (Claim58.lean).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.InRunAll

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (tenOf w1Of W1 sum3Of)
open VerifiableInference.Desc.First.Att.P.Runs (W JoinsP)

variable {K : ℕ}

/-- Where lessPieces returns, what each piece's form asks holds of every piece. -/
theorem rc_lessPieces (start : Aff) (pw : Array W1) (f : W1 → W Aff) (C : W1 → Prop)
    (hf : ∀ w, RC K (f w) (C w)) : RC K (P.Runs.lessPieces start pw f) (∀ w ∈ pw.toList, C w) := by
  unfold P.Runs.lessPieces
  rw [← Array.foldlM_toList]
  exact RC.foldlM_all (fun _ w => RC.left (hf w)) _ _

/-- The same by the pieces' numbers, in the letters of OnBytes/Model. -/
theorem pieces_by_number {pw : Array PW} {C : ℕ → ℕ → Prop}
    (H : ∀ w ∈ (w1Of pw).toList, C w.lam w.a) :
    ∀ b < pw.size, C (pw.getD b default).lam (pw.getD b default).a := by
  intro b hb
  have hs : b < (w1Of pw).size := by
    unfold w1Of
    rw [Array.size_map]
    exact hb
  have hm : (w1Of pw).getD b default ∈ (w1Of pw).toList := by
    rw [Array.mem_toList_iff, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs]
    exact Array.getElem_mem hs
  have e := H _ hm
  rw [getD_lam, getD_a] at e
  exact e

variable (h : Attention.Heard)

/-! ## The premises -/

/-- At a plane claim: the columns read lie in the table on "as". -/
def PlaneIn (pc : PlaneClaim) : Prop :=
  ∀ jj < pc.np, ∀ b < pc.pw.size,
    ∀ hi < (eqTab (pc.z.extract 0 ((if pc.isD then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
      Rows.planeFirst h.S jj (pc.pw.getD b default).lam (pc.pw.getD b default).a pc.isD >>>
        h.S.cf.lmS + hi < (h.t.tabLen.lookup h.t.tA).getD 0

/-- At a unit's scalar on the row maxima. -/
def MaxIn (k : Score) (tM : ℕ) : Prop :=
  ∀ b < k.pw.size, ∀ g < h.S.G, ∀ l < 4,
    h.S.oMr + (l * h.S.Lam + (k.pw.getD b default).lam) * h.S.cf.H +
      (g * h.S.HA + (k.pw.getD b default).a) < (h.t.tabLen.lookup tM).getD 0

/-- At a segment whose scalars read the high parts of the two remainders. -/
def HighIn (pw : Array PW) (zc : Array E) : Prop :=
  (∀ b < pw.size, InLongG h h.t.tO (atRh h.S) (pw.getD b default).lam
    (fun g => g * h.S.HA + (pw.getD b default).a) zc) ∧
  ∀ b < pw.size, InLongG h h.t.tO (atRhp h.S) (pw.getD b default).lam
    (fun g => g * h.S.HA + (pw.getD b default).a) zc

/-- At the denominator. -/
def DenIn : Prop :=
  ∀ b < h.d.pwW.size, ∀ g < h.S.G, ∀ l < 4,
    h.S.oZr + (l * h.S.Lam + (h.d.pwW.getD b default).lam) * h.S.cf.H +
      (g * h.S.HA + (h.d.pwW.getD b default).a) < (h.t.tabLen.lookup h.t.hW).getD 0

/-- At the index's bits. -/
def BitIn : Prop :=
  ∀ k < h.S.cf.lt, ∀ b < h.d.pwX.size, ∀ g < h.S.G, ∀ l < 1,
    h.S.oIb + (l * h.S.Lam + (h.d.pwX.getD b default).lam) * (h.S.cf.lt * h.S.cf.H) +
      (k * h.S.cf.H + g * h.S.HA + (h.d.pwX.getD b default).a) <
        (h.t.tabLen.lookup h.t.hX).getD 0

/-! ## The plane claims -/

theorem rc_linPlanes (pc : PlaneClaim) :
    RC K (P.Runs.linPlanes (inOld h) (remOf pc)) (PlaneIn h pc) := by
  intro acc x hx jj hj
  refine pieces_by_number (C := fun lam a =>
    ∀ hi < (eqTab (pc.z.extract 0 ((if pc.isD then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
      Rows.planeFirst h.S jj lam a pc.isD >>> h.S.cf.lmS + hi <
        (h.t.tabLen.lookup h.t.tA).getD 0) ?_
  unfold P.Runs.linPlanes at hx
  exact RC.forM_mem (a := jj) (RC.left (rc_lessPieces _ _ _ _ fun w =>
    rc_plane h h.t.tA jj w.lam w.a pc.z pc.isD)) (List.mem_range.2 hj) acc x hx

/-- **Where "first" returns: at a plane claim of a visited remainder-table call.** -/
theorem in_planeKR {x : List Aff × JoinsP} (h1 : P.Runs.firstRun (inOld h) K = some x) {c : ACall}
    {q : ℕ} (hc : (c, q) ∈ h.S.calls.toList.zipIdx) (hk : (c.kind == Table.kr) = true)
    {pc : PlaneClaim} (hp : pc ∈ h.planes.toList) (hq : (pc.call == q) = true) : PlaneIn h pc := by
  unfold P.Runs.firstRun P.Runs.gather at h1
  simp only [Option.map_eq_some_iff] at h1
  obtain ⟨_, ⟨y, hy, _⟩, _⟩ := h1
  refine RC.left (K := K) ?_ #[] y hy
  unfold P.Runs.claim3
  show RC K ((P.geoOf h.S).calls.toList.zipIdx.foldlM _ _) _
  rw [calls_zip]
  refine RC.foldlM (a := (P.callOf c, q)) (fun s => ?_) (List.mem_map.2 ⟨(c, q), hc, rfl⟩) _
  rw [if_pos (by rw [← tab_eq c.kind Table.kr] at hk; exact hk)]
  refine RC.left ?_
  unfold P.Runs.callKR
  rw [planes_inOld, ← Array.foldlM_toList, Array.toList_map]
  refine RC.foldlM (a := remOf pc) (fun s => ?_) (List.mem_map.2 ⟨pc, hp, rfl⟩) _
  rw [if_pos (show ((remOf pc).call == (P.callOf c, q).2) = true from hq)]
  exact RC.left (rc_linPlanes h pc)

/-! ## The softmax-table units -/

theorem rc_unitKFD_lin (n : ℕ) (k : Score) {tb : ScoreTables} (ht : h.t.score[n]? = some tb)
    {pc : PlaneClaim} (hp : h.planes[k.claim]? = some pc) :
    RC K (P.Runs.unitKFD (inOld h) n (scoreOf k)) (PlaneIn h pc ∧ MaxIn h k tb.tM) := by
  unfold P.Runs.unitKFD
  dsimp only
  rw [scoreT_inOld, Array.getElem?_map, ht]
  show RC K (P.Runs.W.need (some (scoreTOf tb)) >>= _) _
  rw [show (P.Runs.W.need (some (scoreTOf tb)) : W _) = pure (scoreTOf tb) from rfl, pure_bind]
  rw [planes_inOld, Array.getElem?_map]
  show RC K (P.Runs.W.need (Option.map remOf h.planes[k.claim]?) >>= _) _
  rw [hp]
  show RC K (P.Runs.W.need (some (remOf pc)) >>= _) _
  rw [show (P.Runs.W.need (some (remOf pc)) : W _) = pure (remOf pc) from rfl, pure_bind]
  refine RC.and (rc_linPlanes h pc) fun _ => RC.left ?_
  exact (rc_lessPieces _ _ _ _ fun w => rc_readMaximum h tb.tM k.zg w.lam w.a).mono fun H =>
    pieces_by_number (C := fun lam a => ∀ g < h.S.G, ∀ l < 4,
      h.S.oMr + (l * h.S.Lam + lam) * h.S.cf.H + (g * h.S.HA + a) <
        (h.t.tabLen.lookup tb.tM).getD 0) H

/-- **Where "first" returns: at a visited softmax-table unit, with its plane claim.** -/
theorem in_unitLin {x : List Aff × JoinsP} (h1 : P.Runs.firstRun (inOld h) K = some x) {c : ACall}
    {q : ℕ} (hc : (c, q) ∈ h.S.calls.toList.zipIdx) (hk : (c.kind == Table.kfd) = true) {k : Score}
    {n : ℕ} (hn : (k, n) ∈ h.scores.toList.zipIdx) (hq : (k.call == q) = true) {tb : ScoreTables}
    (ht : h.t.score[n]? = some tb) {pc : PlaneClaim} (hp : h.planes[k.claim]? = some pc) :
    PlaneIn h pc ∧ MaxIn h k tb.tM := by
  unfold P.Runs.firstRun P.Runs.gather at h1
  simp only [Option.map_eq_some_iff] at h1
  obtain ⟨_, ⟨y, hy, _⟩, _⟩ := h1
  refine RC.right (K := K) (fun j3 => RC.left (k := fun j => P.Runs.claim5 (inOld h) j) ?_) #[] y hy
  unfold P.Runs.claim4
  show RC K ((P.geoOf h.S).calls.toList.zipIdx.foldlM _ _) _
  rw [calls_zip]
  refine RC.foldlM (a := (P.callOf c, q)) (fun s => ?_) (List.mem_map.2 ⟨(c, q), hc, rfl⟩) _
  rw [if_pos (by rw [← tab_eq c.kind Table.kfd] at hk; exact hk)]
  refine RC.left ?_
  unfold P.Runs.callKFD
  rw [scores_zip]
  refine RC.foldlM (a := (scoreOf k, n)) (fun s => ?_) (List.mem_map.2 ⟨(k, n), hn, rfl⟩) _
  rw [if_pos (show ((scoreOf k, n).1.call == (P.callOf c, q).2) = true from hq)]
  exact RC.left (rc_unitKFD_lin h n k ht hp)

/-! ## Claim 5 -/

theorem rc_high (start : Aff) (X : TenAt) (pw : Array PW) (zg zc : Array E) :
    RC K (P.Runs.lessPieces start (w1Of pw) fun w =>
      P.Runs.readHead (inOld h) h.t.tO (tenOf X) zg zc w.lam w.a)
      (∀ b < pw.size, InLongG h h.t.tO X (pw.getD b default).lam
        (fun g => g * h.S.HA + (pw.getD b default).a) zc) :=
  (rc_lessPieces _ _ _ _ fun w => rc_readHead h h.t.tO X zg zc w.lam w.a).mono fun H =>
    pieces_by_number (C := fun lam a => InLongG h h.t.tO X lam (fun g => g * h.S.HA + a) zc) H

theorem rc_claim5_lin (j : JoinsP) : RC K (P.Runs.claim5 (inOld h) j)
    (DenIn h ∧ HighIn h h.d.pwW h.d.zcW ∧ HighIn h h.d.pwH h.d.zcH) := by
  unfold P.Runs.claim5
  refine (RC.and ((rc_lessPieces _ _ _ _ fun w =>
      rc_readDenominator h h.t.hW h.d.zgW w.lam w.a).mono fun H =>
        pieces_by_number (pw := h.d.pwW) (C := fun lam a => ∀ g < h.S.G, ∀ l < 4,
          h.S.oZr + (l * h.S.Lam + lam) * h.S.cf.H + (g * h.S.HA + a) <
            (h.t.tabLen.lookup h.t.hW).getD 0) H) fun _ =>
    RC.and (rc_high h _ (atRh h.S) h.d.pwW h.d.zgW h.d.zcW) fun _ =>
    RC.and (rc_high h _ (atRhp h.S) h.d.pwW h.d.zgW h.d.zcW) fun _ =>
    RC.and (rc_high h _ (atRh h.S) h.d.pwH h.d.zgH h.d.zcH) fun _ =>
    RC.left (rc_high h _ (atRhp h.S) h.d.pwH h.d.zgH h.d.zcH)).mono
    fun ⟨a, b, c, d, e⟩ => ⟨a, ⟨b, c⟩, ⟨d, e⟩⟩

theorem rc_claim5_bits (j : JoinsP) {k : ℕ} (hk : k < h.S.cf.lt) : RC K (P.Runs.claim5 (inOld h) j)
    (∀ b < h.d.pwX.size, ∀ g < h.S.G, ∀ l < 1,
      h.S.oIb + (l * h.S.Lam + (h.d.pwX.getD b default).lam) * (h.S.cf.lt * h.S.cf.H) +
        (k * h.S.cf.H + g * h.S.HA + (h.d.pwX.getD b default).a) <
          (h.t.tabLen.lookup h.t.hX).getD 0) := by
  unfold P.Runs.claim5
  iterate 8 (refine RC.right fun _ => ?_)
  refine RC.left (RC.forIn_mem (a := k) (fun _ => by
    repeat (first | exact Yl.pure | refine Yl.bind fun _ => ?_)) ?_ (List.mem_range.2 hk))
  exact RC.left ((rc_lessPieces _ _ _ _ fun w =>
    rc_readIndexBit h h.t.hX h.d.zgX w.lam w.a k).mono fun H =>
      pieces_by_number (pw := h.d.pwX) (C := fun lam a => ∀ g < h.S.G, ∀ l < 1,
        h.S.oIb + (l * h.S.Lam + lam) * (h.S.cf.lt * h.S.cf.H) + (k * h.S.cf.H + g * h.S.HA + a) <
          (h.t.tabLen.lookup h.t.hX).getD 0) H)

/-- **Where "first" returns: at claim 5's linear claims.** -/
theorem in_five {x : List Aff × JoinsP} (h1 : P.Runs.firstRun (inOld h) K = some x) :
    DenIn h ∧ HighIn h h.d.pwW h.d.zcW ∧ HighIn h h.d.pwH h.d.zcH ∧ BitIn h := by
  obtain ⟨a, b, c⟩ := first_rc5 h (fun j => rc_claim5_lin (K := K) h j) h1
  exact ⟨a, b, c, fun k hk => first_rc5 h (fun j => rc_claim5_bits (K := K) h j hk) h1⟩

end K5Law

#print axioms K5Law.in_planeKR
#print axioms K5Law.in_unitLin
#print axioms K5Law.in_five
