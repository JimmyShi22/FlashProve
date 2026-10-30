-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PortTopV.lean: kind K5: hj_top
(Johnson/Desc/First/Att/Claims/PortTop.lean) with one premise on worths in the place of two on
letters.

Main name:
  `hj_top_v`: the join's claim joinF Q u holds at (P.msg m, ul), from the lookup's one claim of the
    run "join": as hj_top, with hjv: for every four numbers w, joinVal (qAt ρ gL) w (the worth of
    gL.cEnd) = joinVal (Q.q u.x) w ((Q.ce u.x).val (P.msg m)), in the place of hq and hce. Why:
    Johnson/Desc/First/Att/Claims/PortJoinV.lean's head.
Premises: as hj_top's, but for hq and hce; hjv is not shown in this file or in what it imports.
Limit: UsualCalls (in PlanLaw) is no test of the verifier: at another call list this file says
nothing.
Of OnBytes and Johnson/Road no routine that runs in a context is named, and no theorem on such a
routine's return; the runs spoken of are the kind's own (Johnson/Desc/First/Att/RunsP.lean).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.PortTop
import Johnson.Desc.First.Att.Claims.PortJoinV

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.K.Kc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ScoreP geoOf)
open VerifiableInference.Desc.First.Att.P.Runs (JoinsP PadIn)
open Cb.Pv.Att (OwnPar)
open Cb.Pv.Att.End (JoinLay joinF joinVal)

variable {Kf : Type} [Field Kf] [Fintype Kf] {ρ : Reading Kf} {W : World Kf} {M X : Type}
  {Pp : OwnPar Kf M X} {u : Pp.Run} {m : M}
  {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Model.Forest.Shape} {zx zy : Array E}
  {zk : Array (Array E)} {gL : Forest.Heard} {i : P.Runs.In} {K : ℕ} {l₁ : List Aff} {j : JoinsP}
  {hh : P.Heard} {L' : P.Left} {a1 a2 : ℕ} {k1 k2 : ScoreP}
  {J₂ : Type} [Fintype J₂] [DecidableEq J₂] {ul : J₂ → Kf}

/-- **hj: the join's claim of the library's ledger**, from the lookup's one claim of the run "join", with hjv in the place of hq and hce. -/
theorem hj_top_v (A : Plan) {Q : JoinLay Pp} {k3 : PadIn} {kf : Array Aff}
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
    (v : x.1.value ρ W = 0) :
    (joinF (J₂ := J₂) Q u).Holds (Sum.elim (Pp.msg m) ul) := by
  have KP := key_pub (gL := gL) (a1 := a1) (a2 := a2) Q.scl hscl N hid PL.usual PL.fit Lk hK PL.place hg hP
    hk1 hk2 (first_at_old hg hz h1) PL.key hzk
  rw [← hC] at KP
  exact join_of_runs_v A hg hz hN h1 hk (callsAre_of PL.place hg hP ha1 ha2 hk1 hk2) hD hnpl N Sl KP gL hjv
    hx v

end K5Law
