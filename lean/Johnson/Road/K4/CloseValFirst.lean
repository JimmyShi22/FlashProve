-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/CloseValFirst.lean: AT EVERY WRITTEN TRANSCRIPT OVER K4's DECLARED ROUNDS, IN THE
FIRST GROUP: WHAT THE FIRST VALUE's TYPED CHAIN PUTS OUT ON THE TRANSCRIPT's IMAGE IS, BY NAME, THE
STATEMENT `TailH.z7` OF THE WORDS ON THE TAPE AND OF SEVEN STATES AND TARGETS a AT WHICH
`TailH.Claims` HOLDS; AND, WHERE K4's HEARING RETURNS ON THAT TAPE, THE COEFFICIENT OF THE TERMS'
SUMCHECK IN IT IS NOT 0. The twin of
Johnson/Road/K4/CloseVal.lean. Glue between files that are proved elsewhere: no new argument, no
count.

  `tb3 t`: the tape behind the three points' rounds. `tb3_eq`: it is `t.drop (k0 g)` in the first
    group.
  `x3Of Q x t`: the first statement x with the three points, each read off its round of the tape.
  `Plan4F.tailMKF`, `Plan4F.tailMKF_ok`: the ties inside `Plan4F.mapsK4F` (PlanMapsFirst.lean), and
    that they are as asked.
  `Plan4F.nz_atF`: on the tape of a written transcript over K4's declared rounds no further
    challenge reads 0.
  `Plan4F.val_atF`: at any list ds with e : ds = dsFirst par, any written transcript τ over ds and
    any entries es: under `TailH.Claims` at the data read off tb3 of the tape
    t0 := tapeW noDigest ds τ es: the chain's value on ((mapsK4F A N Ex).castD e).view τ is
    (tailT … (tb3 t0) …).z7 (x3Of Q x t0) (`k4_valF`, Johnson/Road/K4/OwnFirst.lean).
  `Plan4F.coin_atF`: if moreover every drawn word of t0 is below the prime and K4's hearing returns
    on t0: the coefficient drawn in the sumcheck of the terms, as the chain reads it, is not 0
    (`own_callsG`, OwnRecsG.lean; `tail_coin`, OwnAt.lean).

Limits. `TailH.Claims` IS A PREMISE (seven equations), AT LETTERS a THAT COME OFF NO TAPE: there are
such a at every tape, with no premise (`claims_exist`): so `val_atF` at SOME a says
nothing of K4's records. `Plan4F.MeetsF` is a premise. The first group. Nothing on rows, slots or
worlds; the embedding's claim is not spoken of.
-/
import Johnson.Road.K4.CloseVal
import Johnson.Road.K4.PlanMapsFirst
import Johnson.Road.K4.OwnFirst
import Johnson.Road.K4.OwnAt
import Johnson.Road.K4.OwnRecsG

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb TWhole Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At
open Cb.Pv.Lay.End.Gated (tailW)
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.Desc.First.K4
open OnBytes.Model (Fork Forest.Heard)
open OnBytes.Model.Layer (Pub HPlan2 Own)
open OnBytes.Tie.Pv.Lay.Eng (TailH)
open OnBytes.Desc.First.P1 (gl Ks NzT Adds7 TailM TailR TailNums IsTape tapeW drawnOf nzT_of_ds
  tailIsF_at tailT)
open VerifiableInference.Desc (noDigest)
open Inst.Model (Scl)
open _root_.Run (ckP)

/-- The tape behind the three points' rounds. -/
abbrev tb3 (t : Tape) : Tape := ((t.drop 1).drop 1).drop 1

/-- In the first group it is the tape from which `own_callsG`'s calls are named (OwnRecsG.lean). -/
theorem tb3_eq (t : Tape) {g : ℕ} (hg : (g == 0) = true) : t.drop (k0 g) = tb3 t := by
  have e : k0 g = 3 := by simp [k0, hg]
  rw [e]
  simp [tb3, List.drop_drop]

variable [scl : Scl] {M X : Type} {Q : Plan4F Cb.Gl.E M X} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- The first statement with the three points, each read off its round of the tape. -/
noncomputable abbrev x3Of (Q : Plan4F Cb.Gl.E M X) (x : X) (t : Tape) :
    ((X × (Fin Q.fullF.ownF.toOwn.gT → Cb.Gl.E)) × (Fin Q.fullF.ownF.toOwn.gA → Cb.Gl.E)) ×
      (Fin Q.fullF.ownF.toOwn.gB → Cb.Gl.E) :=
  (((x, Johnson.L5.Layers.rd gl Q.fullF.ownF.toOwn.gT (drawnOf t)),
    Johnson.L5.Layers.rd gl Q.fullF.ownF.toOwn.gA (drawnOf (t.drop 1))),
    Johnson.L5.Layers.rd gl Q.fullF.ownF.toOwn.gB (drawnOf ((t.drop 1).drop 1)))

/-- The ties inside `Plan4F.mapsK4F`. -/
noncomputable def Plan4F.tailMKF (A : Q.MeetsF par hS pcl)
    (N : TailNums Q.fullF.ownF.toOwn.tail) :
    TailM Q.fullF.ownF.toOwn.tail (tailR (numsOf par.P par.hp par.g)) :=
  TailM.ofIs
    (tailIsF_at Q.fullF (OnBytes.Model.Verify.layerNumbers par.P par.hp par.g) A.dimIs A.wk A.hg)
    A.written.2.2.2.2 N

theorem Plan4F.tailMKF_ok (A : Q.MeetsF par hS pcl) (N : TailNums Q.fullF.ownF.toOwn.tail) :
    (Plan4F.tailMKF A N).Ok :=
  tailM_ofIs_ok _ _ N (tailR_pieces (numsOf par.P par.hp par.g)).allE

/-- On the tape of a written transcript over K4's declared rounds no further challenge reads 0. -/
theorem Plan4F.nz_atF (A : Q.MeetsF par hS pcl) (tk : Array Nat)
    (τ : Tr (uLT (ckP .two) (dsFirst par))) (es : List Fmt.Entry) :
    NzT Q.fullF.ownF.toOwn.tail (ksOf { par.P with tokv := tk } par.hp)
      (tb3 (tapeW noDigest (dsFirst par) τ es)) :=
  have ht : IsTape noDigest ([rdOf (pointRd .zero par.P.y.h.lt)] ++
      ([rdOf (pointRd .zero (par.P.y.ls + par.P.y.h.lt))] ++
        ([rdOf (pointRd .zero (par.P.y.lPd - par.P.y.ls))] ++
          (tailR (numsOf par.P par.hp par.g)).all))) τ (tapeW noDigest (dsFirst par) τ es) :=
    ⟨es, rfl⟩
  nzT_of_ds keepsWords_noDigest (ks_fit par.P par.hp par.g tk) ht.right.right.right
    A.written.2.2.2.1

/-- **What the first chain puts out at the image of the written transcript, in the words of the
tape.** -/
theorem Plan4F.val_atF (A : Q.MeetsF par hS pcl) (N : TailNums Q.fullF.ownF.toOwn.tail)
    (Ex : ExtSpec) (tk : Array Nat) {ds : List RDT} (e : ds = dsFirst par)
    (τ : Tr (uLT (ckP .two) ds)) (es : List Fmt.Entry)
    (nz : NzT Q.fullF.ownF.toOwn.tail (ksOf { par.P with tokv := tk } par.hp)
      (tb3 (tapeW noDigest ds τ es)))
    (a : Adds7 Q.fullF.ownF.toOwn.tail) (x : X) (y : Ex.Str)
    (hc : (tailT (Plan4F.tailMKF A N) (ksOf { par.P with tokv := tk } par.hp)
      (tb3 (tapeW noDigest ds τ es)) nz a).Claims (x3Of Q x (tapeW noDigest ds τ es))) :
    ((chFF Q.fullF).val Ex (x, y) (((Plan4F.mapsK4F A N Ex).castD e).view τ)).1 =
      (tailT (Plan4F.tailMKF A N) (ksOf { par.P with tokv := tk } par.hp)
        (tb3 (tapeW noDigest ds τ es)) nz a).z7 (x3Of Q x (tapeW noDigest ds τ es)) := by
  subst e
  exact k4_valF Ex Q.fullF.ownF.toOwn (rdOf (pointRd .zero par.P.y.h.lt))
    (rdOf (pointRd .zero (par.P.y.ls + par.P.y.h.lt)))
    (rdOf (pointRd .zero (par.P.y.lPd - par.P.y.ls))) (Plan4F.tailMKF_ok A N)
    (ks_fit par.P par.hp par.g tk) keepsWords_noDigest τ ⟨es, rfl⟩ nz a x y hc

/-- **The coefficient of the terms' sumcheck, as the first chain reads it at a hearing's tape, is
not 0.** -/
theorem Plan4F.coin_atF (A : Q.MeetsF par hS pcl) (N : TailNums Q.fullF.ownF.toOwn.tail)
    (Ex : ExtSpec) (tk : Array Nat) {ds : List RDT} (e : ds = dsFirst par)
    (τ : Tr (uLT (ckP .two) ds)) (es : List Fmt.Entry)
    (nz : NzT Q.fullF.ownF.toOwn.tail (ksOf { par.P with tokv := tk } par.hp)
      (tb3 (tapeW noDigest ds τ es)))
    (a : Adds7 Q.fullF.ownF.toOwn.tail) (x : X) (y : Ex.Str)
    (hc : (tailT (Plan4F.tailMKF A N) (ksOf { par.P with tokv := tk } par.hp)
      (tb3 (tapeW noDigest ds τ es)) nz a).Claims (x3Of Q x (tapeW noDigest ds τ es)))
    (hs : SmallTape (tapeW noDigest ds τ es)) {fo : Forest.Heard} {F G : Fork} {u : Tape}
    {o : Own}
    (h : hear engFl { par.P with tokv := tk } par.hp par.g fo F (tapeW noDigest ds τ es) =
      some (o, G, u)) :
    ((tailW Q.fullF).b3
      ((chFF Q.fullF).val Ex (x, y) (((Plan4F.mapsK4F A N Ex).castD e).view τ)).1).2.eps ≠ 0 := by
  rw [Plan4F.val_atF A N Ex tk e τ es nz a x y hc]
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, v1, v2, v5, u4, u5, cl, _, _, hz,
    _, _, c3, _⟩ := own_callsG h
  rw [tb3_eq _ A.hg] at c3
  exact tail_coin (Plan4F.tailMKF A N) (((hs.drop 1).drop 1).drop 1) c3 hz nz a _ hc

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4F.tailMKF_ok
#print axioms OnBytes.Road.K4.Plan4F.nz_atF
#print axioms OnBytes.Road.K4.Plan4F.val_atF
#print axioms OnBytes.Road.K4.Plan4F.coin_atF
