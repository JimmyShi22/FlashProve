-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PortJoin.lean: kind K5: the join: the fourteenth part of the library's
ledger ownCl (joinF Q u, Cb/Pv/Att/End/Cl.lean), from the lookup's one claim of the run "join"
(joinRun, Johnson/Desc/First/Look/K3Runs.lean, over the kind's key forms; joinF,
Johnson/Desc/First/Look/LookClaims.lean).

Main names:
  `joinW g KF`: the written form of that claim. `joinF_is`: where the lookup's joinF returns, its
    form is joinW and there is one key form a call. `qAt ρ g`: the join's public letters read off
    what the lookup heard. `joinW_val`: at four calls joinW is worth the library's joinVal at these
    letters (join_value, Johnson/Road/HeadJoin.lean).
  `constA`, `late_const`, `hvF_at`, `unitsSix`, `hid_of_slots`: the hidden value under the slot of
    each named scalar that the key forms read is what the library's form hidA of it is worth (from
    SlotsH, Johnson/Desc/First/Att/Claims/PortAll.lean).
  `join_holds`: these put together, by join_cl (Johnson/Road/Rows/AttPortJoin.lean).
  `kf_set_ne`, `kf_set_eq`, `size_set`, `CallsAre h s c0 c1 c2 c3`, `padOf`, `keys_port`: the
    written key forms (joinsT h, Johnson/Desc/First/Att/Claims/Top.lean) are the sums of terms
    kfPort (Johnson/Road/Rows/AttKeyPort.lean), form for form, and they are four.
  `join_of_runs`: at a record of the kind's own: the return of "first" and "keys", CallsAre, SlotsH,
    KeyPub, hq, hce, the return of joinF on the kind's key forms and that one claim's worth 0 give
    (joinF Q u).Holds (Sum.elim (P.msg m) ul).
Premises, not shown in this file or in what it imports: CallsAre: the place has four calls (0: a
remainder-table call with the plane claims pM, pD; 1: a softmax-table call with the units kM, kD; 2:
a call on the numbers below 2^16 that holds wl and ix; 3: the call of wh), and the records' order.
KeyPub (Johnson/Road/Rows/AttKeyAll.lean): 17 public facts. hq: Q.q u.x = qAt ρ g. hce: the worth of
g.cEnd is (Q.ce u.x).val (P.msg m).
Used: join_value, emptyE, join_cl, kfPort, KeyPub, slotVal, slotOf, Units, Joins, the written
Fo.claim3V, claim4V, claim5V, keyKR … keyWH, padTerm, wall; the library's JoinPub, joinVal, joinF,
kfA, hidA, hvF, liftA, late, ReadK. No routine in a context and no theorem on a run.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.HeadJoin
import Johnson.Road.Rows.AttPortJoin
import Johnson.Desc.First.Look.K3Runs
import Johnson.Desc.First.Att.Claims.PortAll
import Johnson.Desc.First.Att.Claims.Any

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law

section Written
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.K.Kc
open VerifiableInference.Desc.First
open Cb.Pv.Att.End (JoinPub joinVal)

/-- The written form of the lookup's claim on the calls' key vectors. -/
def joinW (g : Forest.Heard) (KF : Array Aff) : Aff :=
  (List.range KF.size).foldl
      (fun (f : Aff) c =>
        Aff.addMul f (Aff.ofConst (subE g.alpha (scaleE c.toUInt64 g.theta)) -
          KF.getD c (Aff.ofConst zeroE)) (g.e.getD c zeroE))
      (Aff.ofConst zeroE) + Aff.ofConst (OnBytes.Road.Hd.emptyE g) - g.cEnd

/-- Where the lookup's joinF returns, its form is the written one, and there is one key form a call. -/
theorem joinF_is {g : Forest.Heard} {KF : Array Aff} {F : Fork} {t : Tape} {x : Aff × Fork × Tape}
    (h : Look.joinF g KF F t = some x) : x.1 = joinW g KF ∧ KF.size = g.shape.calls.size := by
  unfold Look.joinF at h
  simp only [bind, Fl.andThen, Fl.must, Look.joinAddedF, Look.paidF, Fl.change, pure, Fl.ret,
    Option.map_some] at h
  split at h
  · rename_i a G u hm
    split at hm
    · rename_i hb
      simp only [Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨_, e1, _⟩ := hm
      subst e1
      simp only [Option.some.injEq] at h
      rw [← h]
      exact ⟨rfl, beq_iff_eq.mp (Bool.and_eq_true _ _ ▸ hb).1⟩
    · cases hm
  · cases h

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {W : World Kf}

/-- The join's public letters, read off what the lookup heard. -/
def qAt (ρ : Reading Kf) (g : Forest.Heard) : JoinPub Kf :=
  ⟨ρ.val g.alpha, ρ.val g.theta, fun c => ρ.val (g.e.getD c.val zeroE), ρ.val (OnBytes.Road.Hd.emptyE g)⟩

/-- **What the join's written form is worth, at four calls**: the library's joinVal at these letters. -/
theorem joinW_val (N : Numerals ρ) (g : Forest.Heard) (KF : Array Aff) (h4 : KF.size = 4) :
    (joinW g KF).value ρ W =
      joinVal (qAt ρ g) (fun c => (KF.getD c.val (Aff.ofConst zeroE)).value ρ W) (g.cEnd.value ρ W) := by
  unfold joinW
  rw [OnBytes.Road.Hd.join_value, h4]
  unfold joinVal qAt
  rw [Fin.sum_univ_eq_sum_range (fun c => ρ.val (g.e.getD c zeroE) *
    (ρ.val g.alpha - (c : Kf) * ρ.val g.theta - (KF.getD c (Aff.ofConst zeroE)).value ρ W)) 4]
  congr 2
  refine sum_congr rfl fun c hc => ?_
  have hc' : c < 4 := mem_range.mp hc
  have e : ρ.val (ofF c.toUInt64) = (c : Kf) := by
    have key : ∀ n : ℕ, n < 4 → ofF n.toUInt64 = Model.ofNat n := by
      intro n hn
      interval_cases n <;> rfl
    rw [key c hc', N.ofNat]
  rw [e]

/-! ### the hidden values of the named scalars -/

section Hid
open Cb.Pv.Att (OwnPar)
open Cb.Pv.Att.End (late hvF val_hvF hv hv_ofFn hidA pick3 placeK ReadK liftA val_liftA)
open Inst.Model.AttSeg (KSc)

variable [Fintype Kf] {M X : Type} {J₂ : Type} [Fintype J₂] [DecidableEq J₂]

/-- Forms that are constants: any values of the late entries are meant values of these. -/
def constA {J₁ : Type} (ul : J₂ → Kf) : J₂ → TWhole.Aff Kf J₁ := fun j => ⟨fun _ => 0, ul j⟩

omit [Fintype Kf] [Fintype J₂] [DecidableEq J₂] in
theorem late_const {J₁ : Type} [Fintype J₁] (ul : J₂ → Kf) (x : J₁ → Kf) :
    late (constA ul) x = Sum.elim x ul := by
  unfold late constA
  congr 1
  funext i
  simp [TWhole.Aff.val]

omit [Fintype Kf] in
theorem hvF_at {J₁ : Type} [Fintype J₁] [DecidableEq J₁] {n : ℕ} (r : Fin n → Kf) (kk : Fin n → J₁)
    (x : J₁ → Kf) (ul : J₂ → Kf) (j : Fin n) :
    (hvF (J₂ := J₂) (List.ofFn r) kk j.val).val (Sum.elim x ul) = r j - x (kk j) := by
  rw [← late_const ul x, val_hvF, hv_ofFn]

variable {Pp : OwnPar Kf M X} {u : Pp.Run} {m : M} {ul : J₂ → Kf} {h : Attention.Heard} {s : Six}

/-- The four of the six that the library's record of units names, with the two units' tables. -/
def unitsSix (h : Attention.Heard) (s : Six) : Units :=
  ⟨s.pM, s.pD, s.kM, s.kD, h.t.score.getD 0 default, h.t.score.getD 1 default⟩

/-- **The hidden value under the slot of each named scalar that the key forms read is what the library's form of it is worth.** -/
theorem hid_of_slots (Sl : SlotsH W h Pp u m s ul) (hnpl : Pp.npl = 2) :
    ∀ k, ReadK Pp.D k → slotVal W h (unitsSix h s) k = (hidA Pp u k).val (Sum.elim (Pp.msg m) ul) := by
  have aM : ∀ (j : ℕ) (hj : j < 3 * Pp.npl + 7),
      (hvF (J₂ := J₂) (List.ofFn u.rM) Pp.kM j).val (Sum.elim (Pp.msg m) ul) =
        u.rM ⟨j, hj⟩ - Pp.msg m (Pp.kM ⟨j, hj⟩) := fun j hj => hvF_at u.rM Pp.kM _ ul ⟨j, hj⟩
  have aD : ∀ (j : ℕ) (hj : j < 7),
      (hvF (J₂ := J₂) (List.ofFn u.rD) Pp.kD j).val (Sum.elim (Pp.msg m) ul) =
        u.rD ⟨j, hj⟩ - Pp.msg m (Pp.kD ⟨j, hj⟩) := fun j hj => hvF_at u.rD Pp.kD _ ul ⟨j, hj⟩
  have aE : ∀ (j : ℕ) (hj : j < 5 + Pp.D.lT + 2),
      (hvF (J₂ := J₂) (List.ofFn u.rE) Pp.kE j).val (Sum.elim (Pp.msg m) ul) =
        u.rE ⟨j, hj⟩ - Pp.msg m (Pp.kE ⟨j, hj⟩) := fun j hj => hvF_at u.rE Pp.kE _ ul ⟨j, hj⟩
  have sE : ∀ (j : ℕ) (hj : j < 5 + Pp.D.lT + 2), W.slot (slotEh h Pp.D.lT j) =
      u.rE ⟨j, hj⟩ - Pp.msg m (Pp.kE ⟨j, hj⟩) := fun j hj => Sl.e ⟨j, hj⟩
  intro k hk
  unfold slotVal hidA
  match k, hk with
  | .cell .m1 jj, hk =>
    have hk' : jj < 3 := hk
    show W.slot (s.pM.s0 + jj) = (hvF (List.ofFn u.rM) Pp.kM jj).val _
    rw [aM jj (by omega)]
    exact Sl.m1 ⟨jj, by omega⟩ hk'
  | .cell .d1 jj, hk =>
    have hk' : jj < 3 := hk
    show W.slot (s.pD.s0 + jj) = (hvF (List.ofFn u.rM) Pp.kM (3 + jj)).val _
    rw [aM (3 + jj) (by omega)]
    have e := Sl.m2 ⟨3 + jj, by omega⟩ (by show 3 ≤ 3 + jj; omega) (by show 3 + jj < 6; omega)
    rw [show (3 + jj - 3) = jj by omega] at e
    exact e
  | .cell .m2 jj, hk =>
    have hk' : jj < 5 := hk
    show W.slot (s.kM.s0 + jj) = (hvF (List.ofFn u.rM) Pp.kM (6 + jj)).val _
    rw [aM (6 + jj) (by omega)]
    have e := Sl.m3 ⟨6 + jj, by omega⟩ (by show 6 ≤ 6 + jj; omega)
    rw [show (6 + jj - 6) = jj by omega] at e
    exact e
  | .cell .d2 jj, hk =>
    have hk' : jj < 5 := hk
    show W.slot (s.kD.s0 + jj) = (hvF (List.ofFn u.rD) Pp.kD jj).val _
    rw [aD jj (by omega)]
    exact Sl.d ⟨jj, by omega⟩
  | .ms .M, _ =>
    show W.slot (s.kM.s0 + 5) = (hvF (List.ofFn u.rM) Pp.kM 11).val _
    rw [aM 11 (by omega)]
    exact Sl.m3 ⟨11, by omega⟩ (by show 6 ≤ 11; omega)
  | .ss .M, _ =>
    show W.slot (s.kM.s0 + 6) = (hvF (List.ofFn u.rM) Pp.kM 12).val _
    rw [aM 12 (by omega)]
    exact Sl.m3 ⟨12, by omega⟩ (by show 6 ≤ 12; omega)
  | .ms .D, _ =>
    show W.slot (s.kD.s0 + 5) = (hvF (List.ofFn u.rD) Pp.kD 5).val _
    rw [aD 5 (by omega)]
    exact Sl.d ⟨5, by omega⟩
  | .ss .D, _ =>
    show W.slot (s.kD.s0 + 6) = (hvF (List.ofFn u.rD) Pp.kD 6).val _
    rw [aD 6 (by omega)]
    exact Sl.d ⟨6, by omega⟩
  | .acc, _ =>
    show W.slot h.d.s5 = (hvF (List.ofFn u.rE) Pp.kE 0).val _
    rw [aE 0 (by omega), ← sE 0 (by omega)]
    unfold slotEh
    rw [if_pos (by omega)]
    rfl
  | .zo, _ =>
    show W.slot (h.d.s5 + 1) = (hvF (List.ofFn u.rE) Pp.kE 1).val _
    rw [aE 1 (by omega), ← sE 1 (by omega)]
    unfold slotEh
    rw [if_pos (by omega)]
  | .zc, _ =>
    show W.slot (h.d.s5 + 2) = (hvF (List.ofFn u.rE) Pp.kE 2).val _
    rw [aE 2 (by omega), ← sE 2 (by omega)]
    unfold slotEh
    rw [if_pos (by omega)]
  | .rh, _ =>
    show W.slot (h.d.s5 + 3) = (hvF (List.ofFn u.rE) Pp.kE 3).val _
    rw [aE 3 (by omega), ← sE 3 (by omega)]
    unfold slotEh
    rw [if_pos (by omega)]
  | .rh', _ =>
    show W.slot (h.d.s5 + 4) = (hvF (List.ofFn u.rE) Pp.kE 4).val _
    rw [aE 4 (by omega), ← sE 4 (by omega)]
    unfold slotEh
    rw [if_pos (by omega)]
  | .ib k, hk =>
    have hk' : k < Pp.D.lT := hk
    show W.slot (h.d.sIB + k) = (hvF (List.ofFn u.rE) Pp.kE (5 + k)).val _
    rw [aE (5 + k) (by omega), ← sE (5 + k) (by omega)]
    unfold slotEh
    rw [if_neg (by omega), if_pos (by omega), show 5 + k - 5 = k by omega]
  | .rg, _ =>
    show W.slot h.d.s5h = (hvF (List.ofFn u.rE) Pp.kE (5 + Pp.D.lT)).val _
    rw [aE (5 + Pp.D.lT) (by omega), ← sE (5 + Pp.D.lT) (by omega)]
    unfold slotEh
    rw [if_neg (by omega), if_neg (by omega), Nat.sub_self]
    rfl
  | .rg', _ =>
    show W.slot (h.d.s5h + 1) = (hvF (List.ofFn u.rE) Pp.kE (5 + Pp.D.lT + 1)).val _
    rw [aE (5 + Pp.D.lT + 1) (by omega), ← sE (5 + Pp.D.lT + 1) (by omega)]
    unfold slotEh
    rw [if_neg (by omega), if_neg (by omega), show 5 + Pp.D.lT + 1 - (5 + Pp.D.lT) = 1 by omega]

open Cb.Pv.Att.End (JoinLay joinF kfA joinA)

/-- **The join's claim of the library's ledger, from the lookup's one claim of the run "join".** g: what the lookup heard; KF: the calls' key forms that the kind hands over. -/
theorem join_holds {Q : JoinLay Pp} (hD : Pp.D = L5.dimOf h.S) (hnpl : Pp.npl = 2) (N : Numerals ρ)
    (Sl : SlotsH W h Pp u m s ul) {sd : ShD} {pad : E}
    (KP : @KeyPub Kf _ ρ Q.scl h (unitsSix h s) Pp.C (Pp.pub0 u.y0) sd pad)
    (g : Forest.Heard) (KF : Array Aff) (h4 : KF.size = 4) (hq : Q.q u.x = qAt ρ g)
    (hkf : ∀ c : Fin 4, (KF.getD c.val (Aff.ofConst zeroE)).value ρ W =
      (kfPort h (unitsSix h s) sd pad c).value ρ W)
    (hce : g.cEnd.value ρ W = (Q.ce u.x).val (Pp.msg m)) (v : (joinW g KF).value ρ W = 0) :
    (joinF (J₂ := J₂) Q u).Holds (Sum.elim (Pp.msg m) ul) := by
  have jv : (joinW g KF).value ρ W = joinVal (Q.q u.x)
      (fun c => (kfPort h (unitsSix h s) sd pad c).value ρ W) (g.cEnd.value ρ W) := by
    rw [joinW_val N g KF h4, hq]
    congr 1
    funext c
    exact hkf c
  have hce' : g.cEnd.value ρ W = (liftA (J₂ := J₂) (Q.ce u.x)).val (Sum.elim (Pp.msg m) ul) := by
    rw [← late_const ul (Pp.msg m), val_liftA]
    exact hce
  have hv := hid_of_slots Sl hnpl
  rw [hD] at hv
  have e := join_cl (scl := Q.scl) KP (Q.q u.x) (joinW g KF) g.cEnd jv (Sum.elim (Pp.msg m) ul)
    (hidA Pp u) (liftA (Q.ce u.x)) hv hce' v
  unfold joinF
  have eD : kfA (scl := Q.scl) Pp.D Pp.C (Pp.pub0 u.y0) (hidA (J₂ := J₂) Pp u) =
      kfA (scl := Q.scl) (L5.dimOf h.S) Pp.C (Pp.pub0 u.y0) (hidA Pp u) :=
    congrArg (fun D => kfA (scl := Q.scl) D Pp.C (Pp.pub0 u.y0) (hidA (J₂ := J₂) Pp u)) hD
  rw [eD]
  exact e

end Hid
end Written

section Keys
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows

/-- The key form of another call stays. -/
theorem kf_set_ne (j : Joins) {q c : ℕ} (v d : Aff) (h : q ≠ c) :
    (j.set q v).kf.getD c d = j.kf.getD c d := by
  unfold Joins.set
  show (j.kf.setIfInBounds q v).getD c d = _
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, if_neg h]

/-- The key form of the call that is set. -/
theorem kf_set_eq (j : Joins) {q : ℕ} (v d : Aff) (h : q < j.kf.size) : (j.set q v).kf.getD q d = v := by
  unfold Joins.set
  show (j.kf.setIfInBounds q v).getD q d = _
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, if_pos rfl, if_pos h]
  rfl

theorem size_set (j : Joins) (q : ℕ) (v : Aff) : (j.set q v).kf.size = j.kf.size := by
  unfold Joins.set
  simp

/-- **The place has four calls**: 0: a remainder-table call with the two plane claims pM, pD; 1: a softmax-table call with the two units kM, kD; 2: a call on the numbers below 2^16 that holds the lists wl and ix; 3: the call of the list wh. Public facts on the plan and on the records' order. -/
structure CallsAre (h : Attention.Heard) (s : Six) (c0 c1 c2 c3 : ACall) : Prop where
  calls : h.S.calls.toList = [c0, c1, c2, c3]
  k0 : c0.kind = .kr
  k1 : c1.kind = .kfd
  k2 : c2.kind = .r16
  k3 : c3.kind = .wh
  wl : c2.holds .wl = true
  ix : c2.holds .ix = true
  qWH : h.d.qWH = 3
  planes : h.planes.toList = [s.pM, s.pD, s.cM, s.cD]
  pM : s.pM.call = 0
  pD : s.pD.call = 0
  cM : s.cM.call = 1
  cD : s.cD.call = 1
  scores : h.scores.toList = [s.kM, s.kD]
  kM : s.kM.call = 1
  kD : s.kD.call = 1

/-- The padding's term of the softmax-table call's key form, as an element. -/
def padOf (h : Attention.Heard) (c1 : ACall) : E :=
  scaleE (c1.call.tauAt c1.call.t0) (subE oneE (wall c1 (h.g.zk.getD 1 #[])))

/-- **The written key forms are the sums of terms kfPort**, form for form. -/
theorem keys_port {h : Attention.Heard} {s : Six} {c0 c1 c2 c3 : ACall} (F : CallsAre h s c0 c1 c2 c3)
    (tM tD : ScoreTables) :
    (joinsT h).kf.size = 4 ∧ ∀ c : Fin 4, (joinsT h).kf.getD c.val (Aff.ofConst zeroE) =
      kfPort h ⟨s.pM, s.pD, s.kM, s.kD, tM, tD⟩ (h.S.shd c1.sh) (padOf h c1) c := by
  have hn : h.S.calls.size = 4 := by rw [← Array.length_toList, F.calls]; rfl
  have e3 : Fo.claim3V h (Joins.empty h.S.calls.size) =
      (Joins.empty 4).set 0 (Aff.ofConst zeroE + keyKR s.pM + keyKR s.pD) := by
    unfold Fo.claim3V Fo.callKRV
    rw [F.calls, F.planes, hn]
    simp [List.zipIdx, F.k0, F.k1, F.k2, F.k3, F.pM, F.pD, F.cM, F.cD]
  have e4 : ∀ j : Joins, Fo.claim4V h j =
      j.set 1 (Aff.ofConst (padOf h c1) + keyKFD (h.S.shd c1.sh) s.kM + keyKFD (h.S.shd c1.sh) s.kD) := by
    intro j
    unfold Fo.claim4V Fo.callKFDV
    rw [F.calls, F.scores]
    simp [List.zipIdx, F.k0, F.k1, F.k2, F.k3, F.kM, F.kD, padTerm, padOf]
  have e5 : ∀ j : Joins, Fo.claim5V h j =
      (j.set 2 (Aff.ofConst zeroE + keyWL h.d + keyIX h.S h.d)).set 3 (keyWH h.d) := by
    intro j
    unfold Fo.claim5V joinR16
    rw [F.calls, F.qWH]
    simp [List.zipIdx, F.k0, F.k1, F.k2, F.k3, F.wl, F.ix]
  unfold joinsT
  rw [e3, e4, e5]
  have z : (Joins.empty 4).kf.size = 4 := by simp [Joins.empty]
  refine ⟨by rw [size_set, size_set, size_set, size_set, z], fun c => ?_⟩
  match c with
  | 0 =>
    show Array.getD _ 0 _ = _
    rw [kf_set_ne _ _ _ (by omega), kf_set_ne _ _ _ (by omega), kf_set_ne _ _ _ (by omega),
      kf_set_eq _ _ _ (by rw [z]; omega)]
    rfl
  | 1 =>
    show Array.getD _ 1 _ = _
    rw [kf_set_ne _ _ _ (by omega), kf_set_ne _ _ _ (by omega),
      kf_set_eq _ _ _ (by rw [size_set, z]; omega)]
    rfl
  | 2 =>
    show Array.getD _ 2 _ = _
    rw [kf_set_ne _ _ _ (by omega), kf_set_eq _ _ _ (by rw [size_set, size_set, z]; omega)]
    rfl
  | 3 =>
    show Array.getD _ 3 _ = _
    rw [kf_set_eq _ _ _ (by rw [size_set, size_set, size_set, z]; omega)]
    rfl
end Keys

section AtRuns
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.K.Kc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (geoOf)
open VerifiableInference.Desc.First.Att.P.Runs (JoinsP PadIn)
open Cb.Pv.Att (OwnPar)
open Cb.Pv.Att.End (JoinLay joinF)

variable {Kf : Type} [Field Kf] [Fintype Kf] {ρ : Reading Kf} {W : World Kf} {M X : Type} {J₂ : Type}
  [Fintype J₂] [DecidableEq J₂] {Pp : OwnPar Kf M X} {u : Pp.Run} {m : M} {ul : J₂ → Kf}
  {S : Attention.Shape} {gL : Forest.Heard} {i : P.Runs.In} {K : ℕ} {l₁ : List Aff} {j : JoinsP}

/-- **hj: the join's claim of the library's ledger, at a record of the kind's own**: from the return of "first" and "keys", the return of the lookup's joinF on the kind's key forms, and that one claim's worth 0. -/
theorem join_of_runs (A : Plan) {Q : JoinLay Pp} {s : Six} {c0 c1 c2 c3 : ACall} {k3 : PadIn} {kf : Array Aff}
    (hg : i.g = geoOf S) (hz : i.zk = gL.zk) (hN : A.NC = S.calls.size)
    (h1 : P.Runs.firstRun i K = some (l₁, j)) (hk : P.Runs.keysRun i k3 j = some kf)
    (F4 : CallsAre (oldOf S gL i) s c0 c1 c2 c3)
    (hD : Pp.D = L5.dimOf S) (hnpl : Pp.npl = 2) (N : Numerals ρ)
    (Sl : SlotsH W (oldOf S gL i) Pp u m s ul)
    (KP : @KeyPub Kf _ ρ Q.scl (oldOf S gL i) (unitsSix (oldOf S gL i) s) Pp.C (Pp.pub0 u.y0)
      (S.shd c1.sh) (padOf (oldOf S gL i) c1))
    (g : Forest.Heard) (hq : Q.q u.x = qAt ρ g) (hce : g.cEnd.value ρ W = (Q.ce u.x).val (Pp.msg m))
    {F : Fork} {t : Tape} {x : Aff × Fork × Tape} (hx : Look.joinF g kf F t = some x)
    (v : x.1.value ρ W = 0) :
    (joinF (J₂ := J₂) Q u).Holds (Sum.elim (Pp.msg m) ul) := by
  have ej := (first_any A S gL i K l₁ j hg hz hN h1).2
  have ek : kf = (joinsT (oldOf S gL i)).kf := by
    rw [keys_is _ _ _ _ hk, ej, ← joinsT_att A _ hN]
    rfl
  obtain ⟨z4, zc⟩ := keys_port F4 ((oldOf S gL i).t.score.getD 0 default)
    ((oldOf S gL i).t.score.getD 1 default)
  rw [(joinF_is hx).1] at v
  exact join_holds hD hnpl N Sl KP g kf (by rw [ek]; exact z4) hq
    (fun c => by rw [ek, zc c]; rfl) hce v

end AtRuns

end K5Law
