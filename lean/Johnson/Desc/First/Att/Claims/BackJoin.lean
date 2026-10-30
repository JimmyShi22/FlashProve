-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/BackJoin.lean: kind K5: join_holds_v, join_of_runs_v
(Claims/PortJoinV.lean) and hj_top_v (Claims/PortTopV.lean) the other way
round: where the join's claim of the library's ledger (joinF Q u) holds, the lookup's one claim of
the run "join" is worth 0.

Main names: `join_back_v`, `join_of_runs_back`, `hj_top_back`.

Premises: as in the three lemmas named, hjv among them: for every four key values the join's worth
at what the lookup heard is its worth at the
letters of Q.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.PortTopV

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.K.Kc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ScoreP geoOf)
open VerifiableInference.Desc.First.Att.P.Runs (JoinsP PadIn)
open Cb.Pv.Att (OwnPar)
open Cb.Pv.Att.End (JoinLay joinF joinVal kfA joinA hidA liftA val_liftA val_joinA val_kfA KF_congr)

variable {Kf : Type} [Field Kf] [Fintype Kf] {ρ : Reading Kf} {W : World Kf} {M X : Type} {J₂ : Type}
  [Fintype J₂] [DecidableEq J₂] {Pp : OwnPar Kf M X} {u : Pp.Run} {m : M} {ul : J₂ → Kf}

theorem join_back_v {h : Attention.Heard} {s : Six} {Q : JoinLay Pp} (hD : Pp.D = L5.dimOf h.S)
    (hnpl : Pp.npl = 2) (N : Numerals ρ) (Sl : SlotsH W h Pp u m s ul) {sd : ShD} {pad : E}
    (KP : @KeyPub Kf _ ρ Q.scl h (unitsSix h s) Pp.C (Pp.pub0 u.y0) sd pad)
    (g : Forest.Heard) (KF : Array Aff) (h4 : KF.size = 4)
    (hjv : ∀ kf : Fin 4 → Kf, joinVal (qAt ρ g) kf (g.cEnd.value ρ W) =
      joinVal (Q.q u.x) kf ((Q.ce u.x).val (Pp.msg m)))
    (hkf : ∀ c : Fin 4, (KF.getD c.val (Aff.ofConst zeroE)).value ρ W =
      (kfPort h (unitsSix h s) sd pad c).value ρ W)
    (H : (joinF (J₂ := J₂) Q u).Holds (Sum.elim (Pp.msg m) ul)) :
    (joinW g KF).value ρ W = 0 := by
  have hce' : (liftA (J₂ := J₂) (Q.ce u.x)).val (Sum.elim (Pp.msg m) ul) = (Q.ce u.x).val (Pp.msg m) := by
    rw [← late_const ul (Pp.msg m), val_liftA]
  have hv := hid_of_slots Sl hnpl
  rw [hD] at hv
  unfold joinF at H
  have eD : kfA (scl := Q.scl) Pp.D Pp.C (Pp.pub0 u.y0) (hidA (J₂ := J₂) Pp u) =
      kfA (scl := Q.scl) (L5.dimOf h.S) Pp.C (Pp.pub0 u.y0) (hidA Pp u) :=
    congrArg (fun D => kfA (scl := Q.scl) D Pp.C (Pp.pub0 u.y0) (hidA (J₂ := J₂) Pp u)) hD
  rw [eD, TWhole.Aff.claim_holds, val_joinA, hce'] at H
  rw [joinW_val N g KF h4, hjv]
  refine Eq.trans ?_ H
  congr 1
  funext c
  rw [val_kfA (scl := Q.scl), hkf c, kfPort_value (scl := Q.scl) W KP c]
  exact KF_congr (scl := Q.scl) (L5.dimOf h.S) Pp.C (Pp.pub0 u.y0) hv c

variable {S : Attention.Shape} {gL : Forest.Heard} {i : P.Runs.In} {K : ℕ} {l₁ : List Aff} {j : JoinsP}

theorem join_of_runs_back (A : Plan) {Q : JoinLay Pp} {s : Six} {c0 c1 c2 c3 : ACall} {k3 : PadIn} {kf : Array Aff}
    (hg : i.g = geoOf S) (hz : i.zk = gL.zk) (hN : A.NC = S.calls.size)
    (h1 : P.Runs.firstRun i K = some (l₁, j)) (hk : P.Runs.keysRun i k3 j = some kf)
    (F4 : CallsAre (oldOf S gL i) s c0 c1 c2 c3)
    (hD : Pp.D = L5.dimOf S) (hnpl : Pp.npl = 2) (N : Numerals ρ)
    (Sl : SlotsH W (oldOf S gL i) Pp u m s ul)
    (KP : @KeyPub Kf _ ρ Q.scl (oldOf S gL i) (unitsSix (oldOf S gL i) s) Pp.C (Pp.pub0 u.y0)
      (S.shd c1.sh) (padOf (oldOf S gL i) c1))
    (g : Forest.Heard)
    (hjv : ∀ w : Fin 4 → Kf, joinVal (qAt ρ g) w (g.cEnd.value ρ W) =
      joinVal (Q.q u.x) w ((Q.ce u.x).val (Pp.msg m)))
    {F : Fork} {t : Tape} {x : Aff × Fork × Tape} (hx : Look.joinF g kf F t = some x)
    (H : (joinF (J₂ := J₂) Q u).Holds (Sum.elim (Pp.msg m) ul)) :
    x.1.value ρ W = 0 := by
  have ej := (first_any A S gL i K l₁ j hg hz hN h1).2
  have ek : kf = (joinsT (oldOf S gL i)).kf := by
    rw [keys_is _ _ _ _ hk, ej, ← joinsT_att A _ hN]
    rfl
  obtain ⟨z4, zc⟩ := keys_port F4 ((oldOf S gL i).t.score.getD 0 default)
    ((oldOf S gL i).t.score.getD 1 default)
  rw [(joinF_is hx).1]
  exact join_back_v hD hnpl N Sl KP g kf (by rw [ek]; exact z4) hjv
    (fun c => by rw [ek, zc c]; rfl) H

variable {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape} {zx zy : Array E}
  {zk : Array (Array E)} {hh : P.Heard} {L' : P.Left} {a1 a2 : ℕ} {k1 k2 : ScoreP}

/-- **The lookup's one claim of the run "join" is worth 0**, from the join's claim of the library's
ledger. -/
theorem hj_top_back (A : Plan) {Q : JoinLay Pp} {k3 : PadIn} {kf : Array Aff}
    (hid : shapeHid lid cf = Except.ok (S, fs)) (PL : PlanLaw cf S fs) (N : Numerals ρ)
    (Lk : LookAll ρ fs zx zy (Pp.pub0 u.y0)) (hK : ∀ q : Fin 4, KeyIs fs zx zy (zk.getD q.val #[]) q)
    (hg : i.g = geoOf S) (hz : i.zk = gL.zk) (hzk : gL.zk = zk) (hN : A.NC = S.calls.size)
    (hP : P.pointsOf i.g zk hh L' = some i.p)
    (ha1 : hh.remainders[0]? = some a1) (ha2 : hh.remainders[1]? = some a2)
    (hk1 : i.p.scores[0]? = some k1) (hk2 : i.p.scores[1]? = some k2)
    (h1 : P.Runs.firstRun i K = some (l₁, j)) (hk : P.Runs.keysRun i k3 j = some kf)
    (hD : Pp.D = L5.dimOf S) (hC : Pp.C = L5.callsOf fs) (hnpl : Pp.npl = 2)
    (hscl : (Q.scl.κ 0).sh = S.cf.sh.getD 0 0)
    (Sl : SlotsH W (oldOf S gL i) Pp u m (sixTop S i zk a1 a2 k1 k2) ul)
    (hjv : ∀ w : Fin 4 → Kf, joinVal (qAt ρ gL) w (gL.cEnd.value ρ W) =
      joinVal (Q.q u.x) w ((Q.ce u.x).val (Pp.msg m)))
    {F : Fork} {t : Tape} {x : Aff × Fork × Tape} (hx : Look.joinF gL kf F t = some x)
    (H : (joinF (J₂ := J₂) Q u).Holds (Sum.elim (Pp.msg m) ul)) :
    x.1.value ρ W = 0 := by
  have KP := key_pub (gL := gL) (a1 := a1) (a2 := a2) Q.scl hscl N hid PL.usual PL.fit Lk hK PL.place hg hP
    hk1 hk2 (first_at_old hg hz h1) PL.key hzk
  rw [← hC] at KP
  exact join_of_runs_back A hg hz hN h1 hk (callsAre_of PL.place hg hP ha1 ha2 hk1 hk2) hD hnpl N Sl KP gL hjv
    hx H

end K5Law

#print axioms K5Law.hj_top_back
