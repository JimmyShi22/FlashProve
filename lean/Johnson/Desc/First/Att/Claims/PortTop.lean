-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PortTop.lean: kind K5: three of the premises of port_cl and port_pull
(Johnson/Desc/First/Att/Claims/PortAll.lean), from the planner's shape, the plan facts, the lookup's
end point and the return of the kind's own functions: at h := oldOf S gL i
(Johnson/Desc/First/Att/Claims/Any.lean) and the six at the shape's own four calls.

Main names:
  `sixTop S i zk a1 a2 k1 k2`: sixPl (Johnson/Desc/First/Att/Claims/Place.lean) at callAt S 0 and
    callAt S 1. `sixTop_eq`: the same in the letters of six_say
    (Johnson/Desc/First/Att/Claims/PortMine.lean). `below_fm`: of the two softmax-table units the
    first lies below the diagonal, the second on it. `first_at_old`.
  `pts_top`: PtsAre. `six_top`: SixSay, with the four places of its letters. `hj_top`: the join's
    claim joinF Q u holds at (P.msg m, ul), from the lookup's one claim of the run "join": its
    form's worth 0.
Premises: shapeHid lid cf = ok (S, fs); PlanLaw cf S fs (Johnson/Desc/First/Att/Claims/PlanLaw.lean:
what a yes of planOkLaw gives); LookAll ρ fs zx zy (P.pub0 u.y0) and KeyIs at the four calls' key
points (Johnson/Desc/First/Att/Claims/LookKeys.lean); i.g = geoOf S; i.zk = gL.zk; gL.zk = zk; the
return of pointsOf, "first", "second" and "keys"; P.D = dimOf S; P.C = callsOf fs; P.npl = 2. For
hj_top also: Numerals ρ; the first shift of Q's table of scales is the group's; SlotsH; hq: Q.q u.x
= qAt ρ gL; hce: the worth of gL.cEnd is (Q.ce u.x).val (P.msg m); the return of Look.joinF gL kf.
One record gL of the lookup serves the padding's wall and the join's letters.
Limits: UsualCalls (in PlanLaw) is no test of the verifier: at another call list this file says
nothing. LookAll, KeyIs, hq and hce are not shown in this file or in what it imports. Look.joinF
(Johnson/Desc/First/Look/LookClaims.lean), a function on a ledger and a tape, is named; its return
is a premise.
Used: Johnson/Desc/First/Att/Claims/PtsOf.lean, KeyPubOf.lean, PlaceOf.lean, KeyNumsOf.lean,
PlanLaw.lean, PortJoin.lean, PortMine.lean, Place.lean; sizes_of_hid. Of OnBytes and Johnson/Road no
routine that runs in a context is named, and no theorem on such a routine's return; the runs spoken
of are the kind's own (Johnson/Desc/First/Att/RunsP.lean).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.PlanLaw
import Johnson.Desc.First.Att.Claims.PortMine

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.K.Kc
open OnBytes.Road.L5 (callAt)
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ScoreP geoOf callOf)
open VerifiableInference.Desc.First.Att.P.Runs (JoinsP PadIn)
open Cb.Pv.Att (OwnPar)
open Cb.Pv.Att.End (JoinLay joinF zT)

variable {Kf : Type} [Field Kf] [Fintype Kf] {ρ : Reading Kf} {W : World Kf} {M X : Type}
  {Pp : OwnPar Kf M X} {u : Pp.Run} {m : M}
  {lid : ℕ} {cf : Attention.Cfg} {S : Attention.Shape} {fs : Model.Forest.Shape} {zx zy : Array E}
  {zk : Array (Array E)} {gL : Forest.Heard} {i : P.Runs.In} {K : ℕ} {l₁ l₂ : List Aff} {j : JoinsP}
  {hh : P.Heard} {L' : P.Left} {a1 a2 : ℕ} {k1 k2 : ScoreP}

/-- The six at the shape's own four calls. -/
def sixTop (S : Attention.Shape) (i : P.Runs.In) (zk : Array (Array E)) (a1 a2 : ℕ) (k1 k2 : ScoreP) : Six :=
  sixPl i zk (callAt S 0) (callAt S 1) a1 a2 k1 k2

/-- In the letters of six_say, with the two units taken at the shape's place. -/
theorem sixTop_eq (hg : i.g = geoOf S) : sixTop S i zk a1 a2 k1 k2 =
    sixAt i.g zk (0, callOf (callAt S 0), .rm) (0, callOf (callAt S 0), .rd) a1 a2 k1 k2
      ((geoOf S).unitAt 1 (callOf (callAt S 1)) .fm) ((geoOf S).unitAt 1 (callOf (callAt S 1)) .fd) := by
  unfold sixTop sixPl
  rw [hg]

/-- Of the two softmax-table units the first lies below the diagonal, the second on it. -/
theorem below_fm (c : P.CallG) : ((geoOf S).unitAt 1 c .fm).below = true ∧
    ((geoOf S).unitAt 1 c .fd).below = false := ⟨rfl, rfl⟩

theorem first_at_old (hg : i.g = geoOf S) (hz : i.zk = gL.zk) (h1 : P.Runs.firstRun i K = some (l₁, j)) :
    P.Runs.firstRun (inOld (oldOf S gL i)) K = some (l₁, j) := by
  rw [← strip_is_old S gL i hg hz]
  exact h1

/-- **PtsAre**, from the planner's shape, the plan facts, the lookup's end point and the runs' return. -/
theorem pts_top (hid : shapeHid lid cf = Except.ok (S, fs)) (PL : PlanLaw cf S fs)
    (Lk : LookAll ρ fs zx zy (Pp.pub0 u.y0)) (hK : ∀ q : Fin 4, KeyIs fs zx zy (zk.getD q.val #[]) q)
    (hg : i.g = geoOf S) (hz : i.zk = gL.zk) (hP : P.pointsOf i.g zk hh L' = some i.p)
    (hk1 : i.p.scores[0]? = some k1) (hk2 : i.p.scores[1]? = some k2)
    (h1 : P.Runs.firstRun i K = some (l₁, j)) (hD : Pp.D = L5.dimOf S) (hC : Pp.C = L5.callsOf fs) :
    PtsAre ρ (oldOf S gL i) Pp u (sixTop S i zk a1 a2 k1 k2) :=
  pts_are hid PL.usual PL.fit Lk hK PL.place hg hP hk1 hk2 (first_at_old hg hz h1) hD hC rfl

omit [Fintype Kf] in
/-- **SixSay**, likewise. -/
theorem six_top (A : Plan) (hid : shapeHid lid cf = Except.ok (S, fs)) (PL : PlanLaw cf S fs)
    (hg : i.g = geoOf S) (hz : i.zk = gL.zk) (hN : A.NC = S.calls.size)
    (hP : P.pointsOf i.g zk hh L' = some i.p) (h1 : P.Runs.firstRun i K = some (l₁, j))
    (h2 : P.Runs.secondRun i K = some l₂) (hZ : AllZero ρ W (l₁ ++ l₂)) :
    ∃ a1 a2 k1 k2, hh.remainders[0]? = some a1 ∧ hh.remainders[1]? = some a2 ∧
      i.p.scores[0]? = some k1 ∧ i.p.scores[1]? = some k2 ∧
      SixSay ρ W (oldOf S gL i) K (sixTop S i zk a1 a2 k1 k2) :=
  six_say A hg hz hN hP h1 h2 hZ (sizes_of_hid hid).G (by rw [hg]; exact place_kr PL.place)
    (by rw [hg]; exact place_scores PL.place)

variable {J₂ : Type} [Fintype J₂] [DecidableEq J₂] {ul : J₂ → Kf}

/-- **hj: the join's claim of the library's ledger**, likewise: from the lookup's one claim of the run "join". -/
theorem hj_top (A : Plan) {Q : JoinLay Pp} {k3 : PadIn} {kf : Array Aff}
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
    (hq : Q.q u.x = qAt ρ gL) (hce : gL.cEnd.value ρ W = (Q.ce u.x).val (Pp.msg m))
    {F : Fork} {t : Tape} {x : Aff × Fork × Tape} (hx : Look.joinF gL kf F t = some x)
    (v : x.1.value ρ W = 0) :
    (joinF (J₂ := J₂) Q u).Holds (Sum.elim (Pp.msg m) ul) := by
  have KP := key_pub (gL := gL) (a1 := a1) (a2 := a2) Q.scl hscl N hid PL.usual PL.fit Lk hK PL.place hg hP
    hk1 hk2 (first_at_old hg hz h1) PL.key hzk
  rw [← hC] at KP
  exact join_of_runs A hg hz hN h1 hk (callsAre_of PL.place hg hP ha1 ha2 hk1 hk2) hD hnpl N Sl KP gL hq hce
    hx v

end K5Law
