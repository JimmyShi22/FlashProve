-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/OwnAt.lean: THE SEVEN TYPED OUTPUTS, THE COEFFICIENT AND THE PENDING ROW AT THE
CHAIN's DATA READ OFF ANY TAPE tb (`tailT W (ksOf P hp) tb nz a`,
OnBytes/Desc/First/P1/TailTape.lean): so in every group: tb is the tape behind the points in front
(`t0.drop (k0 g)`: OwnRecsG.lean). OwnJoint.lean, OwnCoin.lean and OwnPending.lean say the like at
`t0.drop 1`, for six outputs and a later group. Statements and proofs.

  `tail_outs7`: under `Recs6` at tb (OwnRecs.lean), the seventh record's `RecAt`, the seven numbers
    of further scalars, the seven targets and `StgFits` at each stage: `OutIs` at all seven stages.
  `tail_coin`: `k4_coin` (OwnCoin.lean) at tb.
  `pending_iffF`, `WoSaysF`, `tail_pendingF`: the first group's pending row (`OkMoreF`,
    Cb/Pv/Lay/End/LayFirstAt.lean: one claim more in the row weights, `rowWF`), in the merge's
    record's own words.

NO NEW ARGUMENT: `stgT_out` (OwnJoint.lean) seven times; `eps3_z7`; `OutIs`'s fields; `merge_words`
(OwnPending.lean).

Limits. Those of the three files named. `StgFits`, `TailH.Claims`, `SmallTape`, hfv are premises.
THAT THE ROW WEIGHTS ARE WHAT `wo.recs` SPELLS IS NOT SAID. Nothing on soundness.
-/
import Johnson.Road.K4.OwnPending
import Johnson.Road.K4.OwnCoin
import Cb.Pv.Lay.End.LayFirstAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At Cb.Pv.Lay.End
open Cb.Pv.Lay.End.Gated (Pending tailW tenEF)
open OnBytes OnBytes.K.Kc OnBytes.Slice OnBytes.Desc.First.K4
open OnBytes.Model (Fork Psc Level Tsc WsClaim WsForkOut)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.Tie.Pv.Lay (RecAt StgFits OutIs)
open OnBytes.Tie.Pv.Lay.Eng (TailH)
open OnBytes.Desc.First.P1 (gl pscT NzT Adds7 tailT TailM TailR drawnOf levelWs tscWs plainWs
  tapeEps tscIn_heard eps3_z7 array_getD_toList getD_read)
open Inst.Model (Scl)

section Outs
variable {M X : Type}

/-- **The seven typed outputs are the records of `Recs6` and the merge's, read**, at any tape. H1
and tT are letters here: `own_recsG` (OwnRecsG.lean) ties them to the hearing's record. -/
theorem tail_outs7 {T : LayTail GE M X} {R : TailR} (W : TailM T R) {P : Pub} {hp : HPlan2}
    {o : Own} {H1 : Heard} {tT : Tsc} {hd2 : Level} {tb : Tape} {p1 p4 p5 p6 : Psc}
    (r : Recs6 P hp o H1 tT hd2 tb p1 p4 p5 p6)
    (r7 : RecAt (pscT 0 P.wsLay.lk (((ksOf P hp).tcW tb).drop 1))
      (List.replicate P.wsLay.lk (OnBytes.Psc.Weight.plain 3)) P.wsLay.lk 1
      (pscT 0 P.wsLay.lk (((ksOf P hp).tcW tb).drop 1)).v.length o.wo.p)
    (n1 : T.s1.n = 0) (n2 : T.s2.n = 1) (n3 : T.s3.n = 1) (n4 : T.s4.n = 0) (n5 : T.s5.n = 0)
    (n6 : T.s6.n = 0) (n7 : T.s7.n = 0) (nz : NzT T (ksOf P hp) tb) (a : Adds7 T)
    (t1 : a.t1 = p1.target) (t2 : a.t2 = H1.tV.p.target) (t3 : a.t3 = tT.p.target)
    (t4 : a.t4 = p4.target) (t5 : a.t5 = p5.target) (t6 : a.t6 = p6.target)
    (t7 : a.t7 = o.wo.p.target)
    (f1 : StgFits gl T.s1 a.st1 (levelWs P.rd.muV
      (OnBytes.Model.Layer.normsStart P.y H1.sW H1.gp (drawnOf (tb.drop 1)).toArray H1.PV).2
      (OnBytes.Model.orderDefault P.rd.muV)) P.rd.muV 2)
    (f2 : StgFits gl T.s2 a.st2 (tscWs (H1.PV.toList.take P.y.h.lt)) P.y.h.lt 2)
    (f3 : StgFits gl T.s3 a.st3 (tscWs (H1.ztF.toList.take P.y.h.lt)) P.y.h.lt 1)
    (f4 : StgFits gl T.s4 a.st4 (plainWs hp.lamS) hp.lamS 2)
    (f5 : StgFits gl T.s5 a.st5 (levelWs P.rd.muH
      (OnBytes.Model.Layer.downFrom o.K.rs o.K.fin.wD ++ o.H.ztF)
      (OnBytes.Model.orderRange P.rd.muH)) P.rd.muH 2)
    (f6 : StgFits gl T.s6 a.st6 (levelWs P.rd.muH2
      ((drawnOf ((((ksOf P hp).tc5 tb).drop (P.rd.muH + 3)).drop 1)).toArray ++
        OnBytes.Model.Layer.downFrom o.K.rs P.y.lfe ++ tT.r)
      (OnBytes.Model.orderRange P.rd.muH2)) P.rd.muH2 2)
    (f7 : StgFits gl T.s7 a.st7 (List.replicate P.wsLay.lk (OnBytes.Psc.Weight.plain 3))
      P.wsLay.lk 1) :
    OutIs gl (tailT W (ksOf P hp) tb nz a).d1 p1 ∧
      OutIs gl (tailT W (ksOf P hp) tb nz a).d2 H1.tV.p ∧
      OutIs gl (tailT W (ksOf P hp) tb nz a).d3 tT.p ∧
      OutIs gl (tailT W (ksOf P hp) tb nz a).d4 p4 ∧
      OutIs gl (tailT W (ksOf P hp) tb nz a).d5 p5 ∧
      OutIs gl (tailT W (ksOf P hp) tb nz a).d6 p6 ∧
      OutIs gl (tailT W (ksOf P hp) tb nz a).d7 o.wo.p :=
  ⟨stgT_out _ _ _ nz.b1 _ _ n1 r.r1 t1 f1, stgT_out _ _ _ nz.b2 _ _ n2 r.r2 t2 f2,
    stgT_out _ _ _ nz.b3 _ _ n3 r.r3 t3 f3, stgT_out _ _ _ nz.b4 _ _ n4 r.r4 t4 f4,
    stgT_out _ _ _ nz.b5 _ _ n5 r.r5 t5 f5, stgT_out _ _ _ nz.b6 _ _ n6 r.r6 t6 f6,
    stgT_out _ _ _ nz.b7 _ _ n7 r7 t7 f7⟩

/-- **The coefficient of the terms' sumcheck, as the chain reads it, is not 0**, at any tape. -/
theorem tail_coin {T : LayTail GE M X} {R : TailR} (W : TailM T R) {P : Pub} {hp : HPlan2}
    {tb v : Tape} (hs : SmallTape tb) {Z : Array E} {n : ℕ} {F G : Fork} {tT : Tsc}
    (c3 : Fl.tscIn Z P.y.h.lt n 1 F ((((ksOf P hp).tcP tb).drop 1).drop (P.y.h.lt + 3)) =
      some (tT, G, v))
    (hz : isZeroE tT.p.eps = false) (nz : NzT T (ksOf P hp) tb) (a : Adds7 T) (x : X)
    (hc : (tailT W (ksOf P hp) tb nz a).Claims x) :
    (T.ch4.back ((tailT W (ksOf P hp) tb nz a).z7 x)).2.eps ≠ 0 := by
  rw [eps3_z7 gl T _ x hc]
  have e : tT.p.eps = tapeEps ((((ksOf P hp).tcP tb).drop 1).drop (P.y.h.lt + 3)) :=
    (tscIn_heard c3).2.2.2.2.2.2.2.2.1
  have hsm : SmallTape ((((ksOf P hp).tcP tb).drop 1).drop (P.y.h.lt + 3)) :=
    (((((hs.drop 1).drop 1).drop _).drop 1).drop 1).drop _
  show gl.val (tapeEps ((((ksOf P hp).tcP tb).drop 1).drop (P.y.h.lt + 3))) ≠ 0
  rw [e] at hz
  exact gl_ne_of_word (small_eps hsm) hz

end Outs

section First
variable [scl : Scl] {M X : Type}

/-- The first group's pending row at the chain's last statement, in what was heard. -/
theorem pending_iffF (P : FullFPar GE M X) (D : TailH gl (tailW P)) (x : P.ofp.fs.X3) {p : Psc}
    (h7 : OutIs gl D.d7 p) (Ok' : (tailW P).s7.Nx → M → Prop) (m : M) :
    OkMoreF P Ok' (D.z7 x) m ↔
      Pending P.wp0
          (Gated.rowWF P.wp0 (tenEF P) D.d7.st.1.1 D.d7.st.2
            fun i => gl.val (D.d7.H.rs.getD i.1 ([], zeroE)).2)
          (fun i => gl.val (D.d7.H.rs.getD i.1 ([], zeroE)).2) (gl.val D.d7.H.beta) (D.d7.v ())
          (P.msg m) ∧ Ok' (D.z7 x) m := by
  have e1 : (noKept P.wf.L.Sm).outPt P.wf.L.Mk D.d7.out =
      fun i => gl.val (D.d7.H.rs.getD i.1 ([], zeroE)).2 := funext h7.pt
  have e2 : (noKept P.wf.L.Sm).outB P.wf.L.Mk D.d7.out = gl.val D.d7.H.beta := h7.last
  have e3 : D.d7.out.vals () = D.d7.v () := congrFun h7.vals ()
  exact and_congr (pending_congr P.wp0 (P.msg m) (congrArg (Gated.rowWF P.wp0 (tenEF P) _ _) e1) e1
    e2 e3) Iff.rfl

/-- **The named sentence in the first group.** st: the claims' state; α: the element that combines
the claims. -/
def WoSaysF (P : FullFPar GE M X) (st : St7 GE P.wp0.n) (α : GE) (wo : WsForkOut) (m : M) : Prop :=
  Pending P.wp0 (Gated.rowWF P.wp0 (tenEF P) st α fun i => gl.val (wo.rm.getD i.1 zeroE))
    (fun i => gl.val (wo.rm.getD i.1 zeroE)) (gl.val wo.beta) (gl.val wo.fvp) (P.msg m)

/-- **The first group's pending row at the data read off a tape is the named sentence.** -/
theorem tail_pendingF (Q : FullFPar GE M X) {R : TailR} (W : TailM (tailW Q) R) {P : Pub}
    {hp : HPlan2} {tb u5 u : Tape} {cl : Array WsClaim} {sv : Array Nat} {F G : Fork}
    {wo : WsForkOut} (h : flatForkEnd P.wsLay cl sv F u5 = some (wo, G, u))
    (h5 : u5.drop 1 = ((ksOf P hp).tcW tb).drop 1) (n7 : (tailW Q).s7.n = 0)
    (nz : NzT (tailW Q) (ksOf P hp) tb) (a : Adds7 (tailW Q)) (x : Q.ofp.fs.X3) {p : Psc}
    (h7 : OutIs gl (tailT W (ksOf P hp) tb nz a).d7 p)
    (hfv : (tailT W (ksOf P hp) tb nz a).d7.v () = gl.val wo.fvp) (m : M) :
    OkMoreF Q (fun _ _ => True) ((tailT W (ksOf P hp) tb nz a).z7 x) m ↔
      WoSaysF Q a.st7.1.1 a.st7.2 wo m := by
  obtain ⟨w1, w2⟩ := merge_words h
  rw [h5] at w1 w2
  have eH : (tailT W (ksOf P hp) tb nz a).d7.H =
      pscT 0 P.wsLay.lk (((ksOf P hp).tcW tb).drop 1) := by
    show pscT (tailW Q).s7.n P.wsLay.lk (((ksOf P hp).tcW tb).drop 1) = _
    rw [n7]
  have ept : (fun i : Fin Q.wp0.k =>
      gl.val ((tailT W (ksOf P hp) tb nz a).d7.H.rs.getD i.1 ([], zeroE)).2) =
      fun i => gl.val (wo.rm.getD i.1 zeroE) := by
    funext i
    rw [eH, array_getD_toList, w1]
    exact congrArg gl.val (getD_read (fun q : List E × E => q.2) _ i.1 ([], zeroE) zeroE rfl)
  rw [pending_iffF Q _ x h7, and_iff_left trivial]
  have eb : gl.val (tailT W (ksOf P hp) tb nz a).d7.H.beta = gl.val wo.beta := by rw [eH, ← w2]
  exact pending_congr Q.wp0 (Q.msg m) (congrArg (Gated.rowWF Q.wp0 (tenEF Q) _ _) ept) ept eb hfv

end First

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.tail_outs7
#print axioms OnBytes.Road.K4.tail_coin
#print axioms OnBytes.Road.K4.pending_iffF
#print axioms OnBytes.Road.K4.tail_pendingF
