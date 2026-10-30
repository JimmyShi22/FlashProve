-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/PortJoinV.lean: kind K5: the join's claim of the library's ledger
(joinF Q u, Cb/Pv/Att/End/Cl.lean) from the lookup's one claim of the run "join", with one premise
on worths in the place of two on letters.

Why: join_holds and join_of_runs (Johnson/Desc/First/Att/Claims/PortJoin.lean) take hq: Q.q u.x =
qAt ρ g, letter for letter. Its first letter is the lookup's challenge alpha, and Q.q is a function
of the caller's statement. So two heard records that meet one Q at one statement have one alpha: at
a caller whose statement holds no alpha, one Q meets hq at all runs only if alpha were a function of
that statement. Nothing says that it is, and we do not expect it. join_holds and join_of_runs are
true and, by all that we see, idle at such a caller. The two premises hq and hce are spent there
only to rewrite the worth joinVal.
Main names:
  `join_holds_v`, `join_of_runs_v`: as join_holds and join_of_runs, with hjv: for every four numbers
    kf, joinVal (qAt ρ g) kf (the worth of g.cEnd) = joinVal (Q.q u.x) kf ((Q.ce u.x).val (P.msg
    m)), in the place of hq and hce.
Premises, not shown in this file or in what it imports: hjv; CallsAre; SlotsH; KeyPub.
Used: as Johnson/Desc/First/Att/Claims/PortJoin.lean; in the place of join_cl its proof's steps:
claim_holds, val_joinA, val_kfA (Cb/Pv/Att/End/Join.lean), KF_congr (Cb/Pv/Att/End/Seam.lean),
kfPort_value (Johnson/Road/Rows/AttKeyPort.lean). Look.joinF
(Johnson/Desc/First/Look/LookClaims.lean), a function on a ledger and a tape, is named; its return
is a premise. Of OnBytes and Johnson/Road no routine that runs in a context is named, and no theorem
on such a routine's return; the runs spoken of are the kind's own
(Johnson/Desc/First/Att/RunsP.lean).

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.PortJoin

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open OnBytes.K.Kc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (geoOf)
open VerifiableInference.Desc.First.Att.P.Runs (JoinsP PadIn)
open Cb.Pv.Att (OwnPar)
open Cb.Pv.Att.End (JoinLay joinF joinVal kfA joinA hidA liftA val_liftA val_joinA val_kfA KF_congr)

variable {Kf : Type} [Field Kf] [Fintype Kf] {ρ : Reading Kf} {W : World Kf} {M X : Type} {J₂ : Type}
  [Fintype J₂] [DecidableEq J₂] {Pp : OwnPar Kf M X} {u : Pp.Run} {m : M} {ul : J₂ → Kf}

/-- **The join's claim of the library's ledger, from the lookup's one claim of the run "join"**: with hjv, on the two sides' worths at every four key forms' worths, in the place of the letters' equations. -/
theorem join_holds_v {h : Attention.Heard} {s : Six} {Q : JoinLay Pp} (hD : Pp.D = L5.dimOf h.S)
    (hnpl : Pp.npl = 2) (N : Numerals ρ) (Sl : SlotsH W h Pp u m s ul) {sd : ShD} {pad : E}
    (KP : @KeyPub Kf _ ρ Q.scl h (unitsSix h s) Pp.C (Pp.pub0 u.y0) sd pad)
    (g : Forest.Heard) (KF : Array Aff) (h4 : KF.size = 4)
    (hjv : ∀ kf : Fin 4 → Kf, joinVal (qAt ρ g) kf (g.cEnd.value ρ W) =
      joinVal (Q.q u.x) kf ((Q.ce u.x).val (Pp.msg m)))
    (hkf : ∀ c : Fin 4, (KF.getD c.val (Aff.ofConst zeroE)).value ρ W =
      (kfPort h (unitsSix h s) sd pad c).value ρ W)
    (v : (joinW g KF).value ρ W = 0) :
    (joinF (J₂ := J₂) Q u).Holds (Sum.elim (Pp.msg m) ul) := by
  have hce' : (liftA (J₂ := J₂) (Q.ce u.x)).val (Sum.elim (Pp.msg m) ul) = (Q.ce u.x).val (Pp.msg m) := by
    rw [← late_const ul (Pp.msg m), val_liftA]
  have hv := hid_of_slots Sl hnpl
  rw [hD] at hv
  unfold joinF
  have eD : kfA (scl := Q.scl) Pp.D Pp.C (Pp.pub0 u.y0) (hidA (J₂ := J₂) Pp u) =
      kfA (scl := Q.scl) (L5.dimOf h.S) Pp.C (Pp.pub0 u.y0) (hidA Pp u) :=
    congrArg (fun D => kfA (scl := Q.scl) D Pp.C (Pp.pub0 u.y0) (hidA (J₂ := J₂) Pp u)) hD
  rw [eD, TWhole.Aff.claim_holds, val_joinA, ← v, joinW_val N g KF h4, hjv, hce']
  congr 1
  funext c
  rw [val_kfA (scl := Q.scl), hkf c, kfPort_value (scl := Q.scl) W KP c]
  exact (KF_congr (scl := Q.scl) (L5.dimOf h.S) Pp.C (Pp.pub0 u.y0) hv c).symm

variable {S : Attention.Shape} {gL : Forest.Heard} {i : P.Runs.In} {K : ℕ} {l₁ : List Aff} {j : JoinsP}

/-- The same at a record of the kind's own: from the return of "first" and "keys", the return of the lookup's joinF on the kind's key forms, and that one claim's worth 0. -/
theorem join_of_runs_v (A : Plan) {Q : JoinLay Pp} {s : Six} {c0 c1 c2 c3 : ACall} {k3 : PadIn} {kf : Array Aff}
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
    (v : x.1.value ρ W = 0) :
    (joinF (J₂ := J₂) Q u).Holds (Sum.elim (Pp.msg m) ul) := by
  have ej := (first_any A S gL i K l₁ j hg hz hN h1).2
  have ek : kf = (joinsT (oldOf S gL i)).kf := by
    rw [keys_is _ _ _ _ hk, ej, ← joinsT_att A _ hN]
    rfl
  obtain ⟨z4, zc⟩ := keys_port F4 ((oldOf S gL i).t.score.getD 0 default)
    ((oldOf S gL i).t.score.getD 1 default)
  rw [(joinF_is hx).1] at v
  exact join_holds_v hD hnpl N Sl KP g kf (by rw [ek]; exact z4) hjv
    (fun c => by rw [ek, zc c]; rfl) v

end K5Law
