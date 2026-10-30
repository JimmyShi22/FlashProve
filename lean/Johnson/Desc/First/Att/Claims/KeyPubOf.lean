-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/KeyPubOf.lean: kind K5: the record KeyPub
(Johnson/Road/Rows/AttKeyAll.lean: what the public numbers in the terms of the key forms read as),
paid at a record of the kind's own: h := oldOf S gL i (Johnson/Desc/First/Att/Claims/Any.lean), the
units unitsSix h (sixPl …) (Johnson/Desc/First/Att/Claims/PortJoin.lean,
Johnson/Desc/First/Att/Claims/Place.lean), the shift's numbers S.shd c1.sh and the padding's term
padOf h c1: the form in which join_of_runs (Johnson/Desc/First/Att/Claims/PortJoin.lean) takes it.

Main names:
  `sumW_LL`: the sum of the pieces' weights is the library's LL. `LE_agree`, `idP_agree`.
  `KeyNums S c1`: five public facts on the plan: the shift of the softmax-table call is the group's
    first; the largest score is the library's; 1 ≤ u0; the call's padding key is u0 2^sh + 2^32 −
    2^sh; every piece of the call is of the list fm or fd. Paid in
    Johnson/Desc/First/Att/Claims/KeyNumsOf.lean.
  `pad_val`: the padding's term reads as (1 − LL m2 − LL d2) (cutC − 2^sh + 2^32): by wall_two
    (Johnson/Desc/First/Att/Claims/Wall.lean) and pieces_old
    (Johnson/Desc/First/Att/Claims/PtsBridge.lean).
  `ties_of`: the two units' and the division's ties (TieM, TieD, Tie5) and the two units' pieces, at
    a place with the four calls of PlaceIs.
  `key_pub`: KeyPub, at any table of scales scl whose first shift is the group's.
Premises of key_pub: those of pts_core (Johnson/Desc/First/Att/Claims/PtsOf.lean); Numerals ρ;
KeyNums S c1; (scl.κ 0).sh = S.cf.sh.getD 0 0; gL.zk = zk (the key points at which pointsOf cut are
the lookup's). None of the public tests is asked by the verifier.
Used: as Johnson/Desc/First/Att/Claims/PtsOf.lean; sumW_value, sum_pieces, ones_agree, scaleE_val;
the library's LL, ones, LE, idP, cutC, Om, Smax. Of OnBytes and Johnson/Road no routine that runs in
a context is named, and no theorem on such a routine's return; the runs spoken of are the kind's own
(Johnson/Desc/First/Att/RunsP.lean).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Lane5KvKey
import Johnson.Desc.First.Att.Claims.PtsOf
import Johnson.Desc.First.Att.Claims.Wall
import Johnson.Desc.First.Att.Claims.PortJoin

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ScoreP geoOf callOf keysOf)
open Inst.Model.AttSeg (Pub Fam Calls Dim LL wp)

variable {Kf : Type} [Field Kf] {ρ : Reading Kf}

/-- The sum of the pieces' weights is the library's LL. -/
theorem sumW_LL {S : Attention.Shape} {C : Calls} {z : ℕ → Kf} {fam : Fam} {pw : Array PW}
    (P : PiecesAll S pw)
    (hw : ∀ b < S.NP, ρ.val (pw.getD b default).wp = wp (L5.dimOf S) C z fam b) :
    ρ.val (sumW pw) = LL (L5.dimOf S) C z fam := by
  rw [sumW_value, sum_pieces P]
  unfold LL
  exact sum_congr rfl fun b hb => hw b (mem_range.mp hb)

theorem LE_agree : ∀ (n : ℕ) {u u' v v' : ℕ → Kf}, (∀ k < n, u k = u' k) → (∀ k < n, v k = v' k) →
    Inst.Model.AttSeg.LE n u v = Inst.Model.AttSeg.LE n u' v'
  | 0, _, _, _, _, _, _ => rfl
  | n + 1, u, u', v, v', hu, hv => by
    unfold Inst.Model.AttSeg.LE
    rw [hu 0 (by omega), hv 0 (by omega),
      LE_agree n (u := Inst.Model.AttSeg.sh u 1) (u' := Inst.Model.AttSeg.sh u' 1)
        (v := Inst.Model.AttSeg.sh v 1) (v' := Inst.Model.AttSeg.sh v' 1)
        (fun k hk => hu (1 + k) (by omega)) (fun k hk => hv (1 + k) (by omega))]

theorem idP_agree {n : ℕ} {u u' : ℕ → Kf} (h : ∀ k < n, u k = u' k) :
    Inst.Model.AttSeg.idP n u = Inst.Model.AttSeg.idP n u' := by
  unfold Inst.Model.AttSeg.idP
  exact sum_congr rfl fun k hk => by rw [h k (mem_range.mp hk)]

/-- **Five facts on the plan that the key forms' law takes**: the shift of the softmax-table call is the group's first; the largest score is the library's; the call's padding key is u0 2^sh + 2^32 − 2^sh. Public facts: a test on the shape decides them. -/
structure KeyNums (S : Attention.Shape) (c1 : ACall) : Prop where
  sh : c1.sh = S.cf.sh.getD 0 0
  Sm : ((S.Smax : ℕ) : ℤ) = Inst.Model.Smax
  u0 : 1 ≤ S.u0
  pad : c1.call.tauAt c1.call.t0 = fOfNat (S.u0 * 2 ^ c1.sh + 2 ^ 32 - 2 ^ c1.sh)
  pcs : ∀ pc ∈ c1.pcs.toList, pc.seg = .fm ∨ pc.seg = .fd

variable {S : Attention.Shape} {fs : Model.Forest.Shape} {c1 : ACall}

/-- **The padding's term of the softmax-table call's key form reads as the library's.** key: the call's key point. -/
theorem pad_val (N : Numerals ρ) (KN : KeyNums S c1) {C : Calls} {z : ℕ → Kf} {key : Array E}
    (hM : ρ.val (sumW (pieces c1 key .fm)) = LL (L5.dimOf S) C z .m2)
    (hD : ρ.val (sumW (pieces c1 key .fd)) = LL (L5.dimOf S) C z .d2) :
    ρ.val (scaleE (c1.call.tauAt c1.call.t0) (subE oneE (wall c1 key))) =
      (1 - LL (L5.dimOf S) C z .m2 - LL (L5.dimOf S) C z .d2) *
        (((Inst.Model.cutC (S.cf.sh.getD 0 0) S.u0 - 2 ^ (S.cf.sh.getD 0 0) + 2 ^ 32 : ℤ)) : Kf) := by
  have hk : ∀ pc ∈ (callOf c1).pcs, pc.keys = P.Keys.fm ∨ pc.keys = P.Keys.fd := by
    intro pc hpc
    unfold callOf at hpc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hpc
    rcases KN.pcs x hx with e | e
    · exact .inl (by show keysOf x.seg = _; rw [e]; rfl)
    · exact .inr (by show keysOf x.seg = _; rw [e]; rfl)
  have hw : ρ.val (wall c1 key) = LL (L5.dimOf S) C z .m2 + LL (L5.dimOf S) C z .d2 := by
    rw [← wall_callOf, wall_two ρ (geoOf S) 1 (callOf c1) key hk, ← hM, ← hD]
    have e1 := pieces_old S 1 c1 .fm key
    have e2 := pieces_old S 1 c1 .fd key
    have e1' : P.piecesOf ((geoOf S).unitAt 1 (callOf c1) .fm) key = P.w1Of (pieces c1 key .fm) := e1
    have e2' : P.piecesOf ((geoOf S).unitAt 1 (callOf c1) .fd) key = P.w1Of (pieces c1 key .fd) := e2
    rw [e1', e2', sumW_w1Of, sumW_w1Of]
  have hle : 2 ^ c1.sh ≤ S.u0 * 2 ^ c1.sh + 2 ^ 32 :=
    Nat.le_add_right_of_le (Nat.le_mul_of_pos_left _ KN.u0)
  have hn : ρ.val (ofF (c1.call.tauAt c1.call.t0)) =
      (((Inst.Model.cutC (S.cf.sh.getD 0 0) S.u0 - 2 ^ (S.cf.sh.getD 0 0) + 2 ^ 32 : ℤ)) : Kf) := by
    rw [KN.pad]
    have e : ofF (fOfNat (S.u0 * 2 ^ c1.sh + 2 ^ 32 - 2 ^ c1.sh)) =
        Model.ofNat (S.u0 * 2 ^ c1.sh + 2 ^ 32 - 2 ^ c1.sh) := rfl
    rw [e, N.ofNat, Nat.cast_sub hle, ← KN.sh]
    unfold Inst.Model.cutC
    push_cast
    ring
  rw [OnBytes.scaleE_val, hn, ρ.sub, ρ.one, hw]
  ring

open VerifiableInference.Desc.First.Att.P.Runs (JoinsP)
open OnBytes.Road.L5 (callAt)

variable {zx zy : Array E} {p : Pub Kf} {zk : Array (Array E)} {gL : Forest.Heard} {i : P.Runs.In}
  {c0 c2 c3 : ACall}

/-- The two units' and the division's ties, and the two units' pieces, at a place with these four calls. -/
theorem ties_of {lid : ℕ} {cf : Attention.Cfg} (hid : shapeHid lid cf = Except.ok (S, fs))
    (hF : L5.CallsFit S fs) (A : LookAll ρ fs zx zy p)
    (hK : ∀ q : Fin 4, KeyIs fs zx zy (zk.getD q.val #[]) q) (Pl : PlaceIs S c0 c1 c2 c3)
    {hh : P.Heard} {L' : P.Left} (hP : P.pointsOf (geoOf S) zk hh L' = some i.p) {k1 k2 : ScoreP}
    (hk1 : i.p.scores[0]? = some k1) (hk2 : i.p.scores[1]? = some k2) :
    TieM ρ S fs k1 p ∧ TieD ρ S fs k2 p ∧ Tie5 ρ S fs i.p.d p ∧ k1.below = true ∧ k2.below = false ∧
      (scoreBack k1).pw = pieces c1 (zk.getD 1 #[]) .fm ∧
      (scoreBack k2).pw = pieces c1 (zk.getD 1 #[]) .fd := by
  have N := norm_of_hid hid
  have Z := sizes_of_hid hid
  have L := look_of A
  have hE : ∀ q : Fin 4, EndsIn (zk.getD q.val #[]) zx := fun q => endsIn_of (hK q)
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
  refine ⟨tieM_of hF L N Z H1 U1 (by rw [c1e]; exact hE 1) (by rw [b1]; rfl),
    tieD_of hF L N Z H2 U2 (by rw [c2e]; exact hE 1) (by rw [b2]; rfl),
    tie5_of hF L N.lt (zk := zk) (fun u ⟨k, hu⟩ => by
      have h4 : u.call < 4 := by
        have := single_call hu
        have e4 : (geoOf S).calls.size = 4 := by
          show (S.calls.map callOf).size = 4
          rw [Array.size_map, ← Array.length_toList, Pl.calls]
          rfl
        omega
      exact hE ⟨u.call, h4⟩) (cut5_of hP), by rw [b1]; rfl, by rw [b2]; rfl, ?_, ?_⟩
  · show pwBack k1'.pw = _
    rw [w1']
    exact pw_back 1 c1 .fm _
  · show pwBack k2'.pw = _
    rw [w2']
    exact pw_back 1 c1 .fd _

/-- **KeyPub, paid**: the record (Johnson/Road/Rows/AttKeyAll.lean) of what the public numbers in the terms of the key forms read as, at a record of the kind's own. scl: any table of scales whose first shift is the group's. -/
theorem key_pub (scl : Inst.Model.Scl) (hsh : (scl.κ 0).sh = S.cf.sh.getD 0 0) (N : Numerals ρ) {lid : ℕ}
    {cf : Attention.Cfg} (hid : shapeHid lid cf = Except.ok (S, fs)) (U : L5.UsualCalls cf)
    (hF : L5.CallsFit S fs) (A : LookAll ρ fs zx zy p)
    (hK : ∀ q : Fin 4, KeyIs fs zx zy (zk.getD q.val #[]) q) (Pl : PlaceIs S c0 c1 c2 c3)
    (hg : i.g = geoOf S) {hh : P.Heard} {L' : P.Left} (hP : P.pointsOf i.g zk hh L' = some i.p)
    {a1 a2 : ℕ} {k1 k2 : ScoreP} (hk1 : i.p.scores[0]? = some k1) (hk2 : i.p.scores[1]? = some k2)
    {K : ℕ} {x : List Aff × JoinsP} (h1 : P.Runs.firstRun (inOld (oldOf S gL i)) K = some x)
    (KN : KeyNums S c1) (hzk : gL.zk = zk) :
    @KeyPub Kf _ ρ scl (oldOf S gL i) (unitsSix (oldOf S gL i) (sixPl i zk c0 c1 a1 a2 k1 k2))
      (L5.callsOf fs) p (S.shd c1.sh) (padOf (oldOf S gL i) c1) := by
  obtain ⟨t1, t2, _, _, t5, t6, t7⟩ := pts_core (gL := gL) (a1 := a1) (a2 := a2) hid U hF A hK Pl hg hP
    hk1 hk2 h1
  rw [hg] at hP
  obtain ⟨T1, T2, T5, b1, b2, eM, eD⟩ := ties_of hid hF A hK Pl hP hk1 hk2
  have Nn := norm_of_hid hid
  have Z := sizes_of_hid hid
  have hl := Z.lnT
  have m2 := sumW_LL t5.pairs t5.w
  have d2 := sumW_LL t6.pairs t6.w
  refine ⟨N, ?_, ?_, Nn.lt, sumW_LL t1.pairs t1.w, sumW_LL t2.pairs t2.w, m2, d2,
    sumW_LL t7.pW t7.wW, sumW_LL t7.pX t7.wX, sumW_LL t7.pH t7.wH, ?_, ?_, T5.chi, ?_, ?_, ?_, ?_⟩
  · show (if k1.below then Attention.Seg.fm else Attention.Seg.fd) = _
    rw [b1]; rfl
  · show (if k2.below then Attention.Seg.fm else Attention.Seg.fd) = _
    rw [b2]; rfl
  · show Inst.Model.AttSeg.ones k1.zs.size (pt ρ k1.zs) = Inst.Model.AttSeg.ones ((L5.dimOf S).lP + 1)
      (Inst.Model.AttSeg.zs (L5.dimOf S) (L5.callsOf fs) p.z)
    have e : (L5.dimOf S).lP + 1 = S.lnT := by show S.lnT - 1 + 1 = S.lnT; omega
    rw [T1.ss, e]
    exact ones_agree T1.s
  · show Inst.Model.AttSeg.LE k2.zj.size (pt ρ k2.zj) (pt ρ k2.zi) = Inst.Model.AttSeg.LE S.cf.lB
      (Inst.Model.AttSeg.zj' (L5.dimOf S) (L5.callsOf fs) p.z)
      (Inst.Model.AttSeg.zi' (L5.dimOf S) (L5.callsOf fs) p.z)
    rw [T2.sj]
    exact LE_agree _ T2.j T2.i
  · show Inst.Model.AttSeg.idP i.p.d.ziX.size (pt ρ i.p.d.ziX) = Inst.Model.AttSeg.idP (L5.dimOf S).lT
      (Inst.Model.AttSeg.xi (L5.dimOf S) (L5.callsOf fs) p.z)
    have e : (L5.dimOf S).lT = S.cf.lt := Nn.lt.symm
    rw [T5.siX, e]
    exact idP_agree T5.iX
  · show (((S.u0 * 2 ^ c1.sh : ℕ)) : Kf) = ((Inst.Model.cutC (scl.κ 0).sh S.u0 : ℤ) : Kf)
    rw [hsh, ← KN.sh]
    unfold Inst.Model.cutC
    push_cast
    ring
  · show (((2 * S.Smax + S.u0 * 2 ^ c1.sh : ℕ)) : Kf) =
      ((2 * Inst.Model.Smax + Inst.Model.cutC (scl.κ 0).sh S.u0 : ℤ) : Kf)
    rw [hsh, ← KN.sh, ← KN.Sm]
    unfold Inst.Model.cutC
    push_cast
    ring
  · have e := pad_val (C := L5.callsOf fs) (z := p.z) (key := zk.getD 1 #[]) N KN
      (by rw [← eM]; exact m2) (by rw [← eD]; exact d2)
    show ρ.val (scaleE (c1.call.tauAt c1.call.t0) (subE oneE (wall c1 (gL.zk.getD 1 #[])))) =
      (1 - _ - _) * ((Inst.Model.cutC (scl.κ 0).sh S.u0 - 2 ^ (scl.κ 0).sh + 2 ^ 32 : ℤ) : Kf)
    rw [hzk, hsh]
    exact e

end K5Law
