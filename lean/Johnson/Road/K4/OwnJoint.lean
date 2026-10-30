-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/OwnJoint.lean: THE JOINT AT K4's TEXT, FOR A GROUP THAT IS NOT THE FIRST: what the
chain of the layers' own rounds puts out at the image of the written transcript is, by name, the
statement `TailH.z7` of the words on the tape that K4's hearing hears; and the typed outputs of the
first six sumchecks in it are the six records of `Recs6` (OwnRecs.lean), read. That these are the
records of K4's own hearing o is `own_calls6`'s and `Chain7`'s there. Statements and proofs.
Bookkeeping over the files named below: no count is made.

  `k4Tail`: the chain's data, read off K4's tape: `tailT` (OnBytes/Desc/First/P1/TailTape.lean) at
    K4's numbers `ksOf P hp` and the tape behind the token point's round.
  `k4_val`: if t0 is the flat tape of the written transcript τ over [dT] ++ R.all: under `TailM.Ok`,
    the numbers' fit, `NzT` and `TailH.Claims`: `(A.ch.val Ex (x, y) (((ownM A dT W).mapsR Ex).view
    τ)).1 = (k4Tail …).z7 (x, the token point)`. The hearing does not occur in it.
  `stgT_out`, `k4_outs6`: under `Recs6` (OwnRecs.lean: `own_recs6` gives it where `hear` returns on
    t0 in a group that is not the first): for all states and targets a whose first six targets are
    the records', and `StgFits` at each stage: `OutIs` (OnBytes/Tie/Pv/Lay/HearTieL.lean) holds of
    each of the six stages' data and its record: the typed output's eps, last value, point, last
    coordinate and end values are the record's and the data's, read.

NO NEW ARGUMENT: `own_val_z7` (OwnView.lean), `tailT_is` (TailTape.lean), `own_recs6`,
`fits_out` (OnBytes/Tie/Pv/Lay/HearTieAll.lean).

Limits. PREMISES: `TailM.Ok` (every message holds elements alone; the stages' numbers), `Ks.Fit`,
`NzT` (no further challenge reads 0), `TailH.Claims`, `StgFits`, the six numbers of further scalars
(0 · 1 · 1 · 0 · 0 · 0): NOTHING HERE SHOWS THAT A VALUE OF THE CHAIN's LETTERS MEETS THEM. THE
SEVENTH SUMCHECK (the merge) HAS NO `OutIs` HERE. One direction. A group that is not the first.
Nothing on what the rows and the slots are worth. NO SOUNDNESS OF ANYTHING IS CLAIMED.
-/
import Johnson.Road.K4.OwnRecs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open Iop Cb TWhole Cb.Pv.Lay Cb.Pv.Att Johnson.L5.Layers
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.Desc.First.K4
open OnBytes.Model (Fork Psc Level Tsc)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.Tie.Pv.Lay (RecAt StgFits OutIs fits_out)
open OnBytes.Tie.Pv.Lay.Eng (StgH TailH)
open OnBytes.Desc.First.P1 (gl Ks NzT Adds7 tailT tailT_is TailM TailR ownM KeepsWords IsTape tapeW
  drawnOf own_val_z7 levelWs tscWs plainWs pscT stgT sentOf)
open _root_.Run (ckP)

variable {M X : Type}

/-- The chain's data, read off K4's tape. -/
def k4Tail {T : LayTail GE M X} {R : TailR} (W : TailM T R) (P : Pub) (hp : HPlan2) (t0 : Tape)
    (nz : NzT T (ksOf P hp) (t0.drop 1)) (a : Adds7 T) : TailH gl T :=
  tailT W (ksOf P hp) (t0.drop 1) nz a

/-- **What the chain puts out at the image of the written transcript, in the words of K4's
tape.** -/
theorem k4_val {X0 : Type} (Ex : ExtSpec) (A : LayOwn GE M X0) (dT : RDT) {R : TailR}
    {W : TailM A.tail R} (ok : W.Ok) {P : Pub} {hp : HPlan2} (hk : (ksOf P hp).Fit R)
    {f : Fmt.RoundView → Fmt.RoundView} (hf : KeepsWords f) (τ : Tr (uLT (ckP .two) ([dT] ++ R.all)))
    {t0 : Tape} (ht : IsTape f ([dT] ++ R.all) τ t0) (nz : NzT A.tail (ksOf P hp) (t0.drop 1))
    (a : Adds7 A.tail) (x : X0) (y : Ex.Str)
    (hc : (k4Tail W P hp t0 nz a).Claims (x, Johnson.L5.Layers.rd gl A.gT (drawnOf t0))) :
    (A.ch.val Ex (x, y) (((ownM A dT W).mapsR Ex).view τ)).1 =
      (k4Tail W P hp t0 nz a).z7 (x, Johnson.L5.Layers.rd gl A.gT (drawnOf t0)) :=
  own_val_z7 Ex A dT ok τ (ht.one hf).2.2 (tailT_is hf W hk ht.right nz a) x y hc

/-- One stage: the typed output of the data read off a tape is the record, read. -/
theorem stgT_out {S : Stg GE M X} (num : S.L.S.A → ℕ) (k : ℕ) (t : Tape)
    (hβ : gl.val (pscT S.n k t).beta ≠ 0) (st : S.L.St) (tg : E) {n : ℕ} (hn : S.n = n)
    {ws : List OnBytes.Psc.Weight} {dY nv : ℕ} {p : Psc} (r : RecAt (pscT n k t) ws k dY nv p)
    (ht : tg = p.target) (f : StgFits gl S st ws k dY) : OutIs gl (stgT num k t hβ st tg) p := by
  subst hn
  exact fits_out gl (stgT num k t hβ st tg) (riders := sentOf t) ⟨rfl, rfl, ht⟩ r f

/-- **The typed outputs of the first six sumchecks are the six records of `Recs6`, read.** H1 and tT
are letters here: `own_recs6` ties them to the hearing's record (o.H = heardOf H1 tT). -/
theorem k4_outs6 {T : LayTail GE M X} {R : TailR} (W : TailM T R) {P : Pub} {hp : HPlan2}
    {o : Own} {H1 : Heard} {tT : Tsc} {hd2 : Level} {t0 : Tape} {p1 p4 p5 p6 : Psc}
    (r : Recs6 P hp o H1 tT hd2 (t0.drop 1) p1 p4 p5 p6)
    (n1 : T.s1.n = 0) (n2 : T.s2.n = 1) (n3 : T.s3.n = 1) (n4 : T.s4.n = 0) (n5 : T.s5.n = 0)
    (n6 : T.s6.n = 0) (nz : NzT T (ksOf P hp) (t0.drop 1)) (a : Adds7 T)
    (t1 : a.t1 = p1.target) (t2 : a.t2 = H1.tV.p.target) (t3 : a.t3 = tT.p.target)
    (t4 : a.t4 = p4.target) (t5 : a.t5 = p5.target) (t6 : a.t6 = p6.target)
    (f1 : StgFits gl T.s1 a.st1 (levelWs P.rd.muV
      (OnBytes.Model.Layer.normsStart P.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray
        H1.PV).2 (OnBytes.Model.orderDefault P.rd.muV)) P.rd.muV 2)
    (f2 : StgFits gl T.s2 a.st2 (tscWs (H1.PV.toList.take P.y.h.lt)) P.y.h.lt 2)
    (f3 : StgFits gl T.s3 a.st3 (tscWs (H1.ztF.toList.take P.y.h.lt)) P.y.h.lt 1)
    (f4 : StgFits gl T.s4 a.st4 (plainWs hp.lamS) hp.lamS 2)
    (f5 : StgFits gl T.s5 a.st5 (levelWs P.rd.muH
      (OnBytes.Model.Layer.downFrom o.K.rs o.K.fin.wD ++ o.H.ztF)
      (OnBytes.Model.orderRange P.rd.muH)) P.rd.muH 2)
    (f6 : StgFits gl T.s6 a.st6 (levelWs P.rd.muH2
      ((drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1)).toArray ++
        OnBytes.Model.Layer.downFrom o.K.rs P.y.lfe ++ tT.r)
      (OnBytes.Model.orderRange P.rd.muH2)) P.rd.muH2 2) :
    OutIs gl (k4Tail W P hp t0 nz a).d1 p1 ∧ OutIs gl (k4Tail W P hp t0 nz a).d2 H1.tV.p ∧
      OutIs gl (k4Tail W P hp t0 nz a).d3 tT.p ∧ OutIs gl (k4Tail W P hp t0 nz a).d4 p4 ∧
      OutIs gl (k4Tail W P hp t0 nz a).d5 p5 ∧ OutIs gl (k4Tail W P hp t0 nz a).d6 p6 :=
  ⟨stgT_out _ _ _ nz.b1 _ _ n1 r.r1 t1 f1, stgT_out _ _ _ nz.b2 _ _ n2 r.r2 t2 f2,
    stgT_out _ _ _ nz.b3 _ _ n3 r.r3 t3 f3, stgT_out _ _ _ nz.b4 _ _ n4 r.r4 t4 f4,
    stgT_out _ _ _ nz.b5 _ _ n5 r.r5 t5 f5, stgT_out _ _ _ nz.b6 _ _ n6 r.r6 t6 f6⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4_val
#print axioms OnBytes.Road.K4.stgT_out
#print axioms OnBytes.Road.K4.k4_outs6
