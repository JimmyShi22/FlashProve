-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/HeadsLedFirst.lean: THE FIRST GROUP's TWINS OF PendingLed.lean, MergeLed.lean AND
HeadsLed.lean. Under the record `LedG` of a hearing of the layers' own rounds in any group
(Johnson/Road/K4/OwnLedgersG.lean), at the letters `tailW P` of the first sub-proof's chain behind
its three points (Cb/Pv/Lay/End/FirstShare.lean) and the chain's data read off the tape behind the
points in front (`t0.drop (k0 g)`) with the states `addsOf` (OnBytes/Desc/First/P1/TailAdds.lean):
the pending row is the named sentence `WoSaysF` (OwnAt.lean) of the hearing's own merge record; the
merge's own claim is worth 0 exactly if `mergeLedF` (Cb/Pv/Lay/End/MergeShare.lean) holds; the three
product layers' rows are worth 0 exactly if `u1At` and `prodU` are, at the stages' typed outputs.
Five statements and their proofs.

NO NEW ARGUMENT: `tail_pendingF` (OwnAt.lean), `stgT_out` (OwnJoint.lean), `merge_recAt`,
`merge_shown`, `merge_row_stg`, `level_row_stg`, `level_row_stgUp` (OwnRowsStage.lean), at `LedG`'s
calls.

Limits. All letters are the caller's. PREMISES: `LedG`; `StgFits` at each stage; the stages'
targets; the numbers of the end values; (D1), (D2). THE GROUP g IS A LETTER: nothing here says that
it is the first; the typed letters are the first sub-proof's. Nothing on the embedding's claim, on
the two further points in front, on the row products' and the batched sumcheck's own rows. The state
`aS7` is typed: that the row weights at it are what `o.wo.recs` spells is not said. One world: no
draw. Nothing on soundness.
-/
import Johnson.Road.K4.OwnRowsStage
import Johnson.Road.K4.OwnAt
import Johnson.Road.K4.OwnLedgersG
import OnBytes.Desc.First.P1.TailAdds
import Cb.Pv.Lay.End.NormsRows
import Cb.Pv.Lay.End.MergeShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb TWhole Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model (Fork Forest.Heard Level Tsc World orderDefault orderRange)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard downFrom normsStart)
open OnBytes.Tie.Pv.Lay (StgFits)
open OnBytes.Desc.First.P1 (gl NzT TailM TailR Tg7 tailT addsOf aD1 aS1 aD5 aS5 aD6 aS6 aS7 drawnOf
  levelRec levelWs plainWs pscT stgT)
open Inst.Model (Scl)

variable [scl : Scl] {M Xs : Type} (P : FullFPar Cb.Gl.E M Xs) {R : TailR}
  (W : TailM (tailW P) R) {Pp : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own}
  {F G : Fork} {t0 u u5 : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {J₂ : Type} [Fintype J₂]

/-- **The first group's pending row at a hearing.** -/
theorem pendingF_of_led (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5
    u5)
    (n7 : (tailW P).s7.n = 0) (nz : NzT (tailW P) (ksOf Pp hp) (t0.drop (k0 g)))
    (x : P.ofp.fs.X3) (g7 : Tg7) (ht7 : g7.t7 = o.wo.p.target)
    (f7 : StgFits gl (tailW P).s7 (aS7 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) (plainWs
        Pp.wsLay.lk)
      Pp.wsLay.lk 1)
    (hnum : W.w7.num () = 0) (m : M) :
    OkMoreF P (fun _ _ => True)
        ((tailT W (ksOf Pp hp) (t0.drop (k0 g)) nz (addsOf W (ksOf Pp hp) (t0.drop (k0 g)) nz x
            g7)).z7 x) m ↔
      WoSaysF P (aS7 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7).1.1 (aS7 W (ksOf Pp hp) (t0.drop (k0
          g)) nz x g7).2
        o.wo m := by
  obtain ⟨cl, c7⟩ := Ld.c7
  have r7 := (merge_recAt c7).1
  rw [Ld.u5d] at r7
  have O7 := stgT_out W.w7.num (ksOf Pp hp).k7 _ nz.b7 (aS7 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
      g7.t7 n7
    r7 ht7 f7
  have hfv : (tailT W (ksOf Pp hp) (t0.drop (k0 g)) nz (addsOf W (ksOf Pp hp) (t0.drop (k0 g)) nz x
      g7)).d7.v () =
      gl.val o.wo.fvp := by
    rw [merge_shown Ld.sG5 c7, Ld.u5d]
    show gl.val ((pscT _ _ (((ksOf Pp hp).tcW (t0.drop (k0 g))).drop 1)).v.getD (W.w7.num ()) _) = _
    rw [hnum]
    rfl
  exact tail_pendingF P W c7 Ld.u5d n7 nz (addsOf W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) x O7 hfv
      m

/-- **The first group's merge's own claim.** -/
theorem mergeF_of_led (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (n7 : (tailW P).s7.n = 0) (nz : NzT (tailW P) (ksOf Pp hp) (t0.drop (k0 g)))
    (x : P.ofp.fs.X3) (g7 : Tg7) (ht7 : g7.t7 = o.wo.p.target)
    (f7 : StgFits gl (tailW P).s7 (aS7 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) (plainWs
        Pp.wsLay.lk)
      Pp.wsLay.lk 1)
    (hnum : W.w7.num () = 0) (Ex : ExtSpec) (y : Ex.Str) (Wd : World Cb.Gl.E)
    (m : P.wp0.J → Cb.Gl.E) (w : J₂ → Cb.Gl.E)
    (D1 : P.wf.L.toSum.T.par.W (aS7 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) m =
      OnBytes.Road.Hd.place Wd.slot
        (P.wf.L.toSum.T.par.vars (aS7 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)) o.wo.p.first)
    (D2 : P.wf.L.toSum.T.par.inc (aS7 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) m =
      gl.val o.wo.p.target - o.wo.p.start.value gl Wd) :
    (o.wo.p.rowForm o.wo.fvp {}).value gl Wd = 0 ↔
      TWhole.Ledger.Holds
        (mergeLedF (J₂ := J₂) P.wp0 (tenEF P) (rhsF P) P.mkE
          ((tailT W (ksOf Pp hp) (t0.drop (k0 g)) nz (addsOf W (ksOf Pp hp) (t0.drop (k0 g)) nz x
              g7)).z7 x).2)
        (Sum.elim m w) := by
  obtain ⟨cl, c7⟩ := Ld.c7
  have hβ : gl.val (pscT (tailW P).s7.n Pp.wsLay.lk (u5.drop 1)).beta ≠ 0 := by
    rw [Ld.u5d]
    exact nz.b7
  have key := merge_row_stg (J₂ := J₂) W.w7.num c7 Ld.sG5 hβ
    (aS7 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) g7.t7 n7 ht7 f7 P.wf.L.pick_ok Ex y Wd m D1 D2
    (fun _ _ => Finset.sum_eq_zero fun b _ => (show Empty from b).elim) () hnum
    (fun z vals => by
      show ([(1 : Cb.Gl.E) * [vals ()].prod]).sum = _
      simp)
    (fun _ b => Empty.elim b) (fun _ _ b _ => Empty.elim b) w
  have eo : (stgT W.w7.num Pp.wsLay.lk (u5.drop 1) hβ (aS7 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
      g7.t7).out =
      ((tailT W (ksOf Pp hp) (t0.drop (k0 g)) nz (addsOf W (ksOf Pp hp) (t0.drop (k0 g)) nz x
          g7)).z7 x).2 := by
    have : ∀ (tt : Tape) (e : tt = ((ksOf Pp hp).tcW (t0.drop (k0 g))).drop 1)
        (hb : gl.val (pscT (tailW P).s7.n Pp.wsLay.lk tt).beta ≠ 0),
        (stgT W.w7.num Pp.wsLay.lk tt hb (aS7 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) g7.t7).out =
          ((tailT W (ksOf Pp hp) (t0.drop (k0 g)) nz (addsOf W (ksOf Pp hp) (t0.drop (k0 g)) nz x
              g7)).z7 x).2 := by
      intro tt e hb
      subst e
      rfl
    exact this _ Ld.u5d hβ
  rw [eo] at key
  unfold mergeLedF
  rw [ledOf_holds]
  exact key.trans ⟨fun h f hf => by rw [List.mem_singleton.1 hf]; exact h,
    fun h => h _ List.mem_cons_self⟩

/-- **The first gated layer's own claim**, at the first sub-proof's letters. -/
theorem gated5F_of_led (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5
    u5)
    (nz : NzT (tailW P) (ksOf Pp hp) (t0.drop (k0 g)))
    (x : P.ofp.fs.X3) (g7 : Tg7)
    (ht5 : g7.t5 = (levelRec Pp.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF)
      (OnBytes.Model.Aff.slot o.K.sH1) (orderRange Pp.rd.muH) G3
      ((ksOf Pp hp).tc5 (t0.drop (k0 g)))).target)
    (f5 : StgFits gl (tailW P).s5 (aS5 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
      (levelWs Pp.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF) (orderRange Pp.rd.muH))
      Pp.rd.muH 2)
    (h0 : W.w5.num false = 0) (h1 : W.w5.num true = 1) (Ex : ExtSpec) (y : Ex.Str)
    (Wd : World Cb.Gl.E) (m : P.fp.gp.J → Cb.Gl.E) (w : J₂ → Cb.Gl.E)
    (D1 : P.fp.gp.toSum.T.par.W (aS5 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) m =
      OnBytes.Road.Hd.place Wd.slot
        (P.fp.gp.toSum.T.par.vars (aS5 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7))
        (levelRec Pp.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF)
          (OnBytes.Model.Aff.slot o.K.sH1) (orderRange Pp.rd.muH) G3
          ((ksOf Pp hp).tc5 (t0.drop (k0 g)))).first)
    (D2 : P.fp.gp.toSum.T.par.inc (aS5 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) m =
      gl.val (levelRec Pp.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF)
          (OnBytes.Model.Aff.slot o.K.sH1) (orderRange Pp.rd.muH) G3
          ((ksOf Pp hp).tc5 (t0.drop (k0 g)))).target -
        (levelRec Pp.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF)
          (OnBytes.Model.Aff.slot o.K.sH1) (orderRange Pp.rd.muH) G3
          ((ksOf Pp hp).tc5 (t0.drop (k0 g)))).start.value gl Wd) :
    o.hd.row.value gl Wd = 0 ↔
      Blocks.Form.val (Sum.elim m w)
        (prodU (J₂ := J₂) P.fp.gp (aD5 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7).out) = 0 := by
  obtain ⟨v5, c5⟩ := Ld.c5
  exact level_row_stg (J₂ := J₂) W.w5.num c5 Ld.s3 nz.b5
    (aS5 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) g7.t5 rfl ht5 f5
    (F₀_ok _ (P.fp.gp.eq0 : Eq0 P.fp.gp.toSum.T.par)) Ex y Wd m D1 D2
    (fun _ _ => Finset.sum_eq_zero fun b _ => (show Empty from b).elim) false true h0 h1
    (fun z vals => by
      show ([(1 : Cb.Gl.E) * [vals false, vals true].prod]).sum = _
      simp)
    (fun _ b => Empty.elim b) (fun _ _ b _ => Empty.elim b) w

/-- **The second gated layer's own claim**, at the first sub-proof's letters. -/
theorem gated6F_of_led (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5
    u5)
    (nz : NzT (tailW P) (ksOf Pp hp) (t0.drop (k0 g)))
    (x : P.ofp.fs.X3) (g7 : Tg7) {p6 : OnBytes.Model.Psc}
    (hp6 : p6 = (levelRec Pp.rd.muH2
      ((drawnOf ((((ksOf Pp hp).tc5 (t0.drop (k0 g))).drop (Pp.rd.muH + 3)).drop 1)).toArray ++
        downFrom o.K.rs Pp.y.lfe ++ tT.r)
      (Road.Rows.start2 Pp.y.LamM o.K.sH1
        (drawnOf ((((ksOf Pp hp).tc5 (t0.drop (k0 g))).drop (Pp.rd.muH + 3)).drop 1)).toArray)
      (orderRange Pp.rd.muH2) G3' ((ksOf Pp hp).tc6 (t0.drop (k0 g)))))
    (ht6 : g7.t6 = p6.target)
    (f6 : StgFits gl (tailW P).s6 (aS6 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
      (levelWs Pp.rd.muH2
        ((drawnOf ((((ksOf Pp hp).tc5 (t0.drop (k0 g))).drop (Pp.rd.muH + 3)).drop 1)).toArray ++
          downFrom o.K.rs Pp.y.lfe ++ tT.r) (orderRange Pp.rd.muH2)) Pp.rd.muH2 2)
    (h0 : W.w6.num false = 0) (h1 : W.w6.num true = 1) (Ex : ExtSpec) (y : Ex.Str)
    (Wd : World Cb.Gl.E) (m : P.fp.rt.L.J → Cb.Gl.E) (w : J₂ → Cb.Gl.E)
    (D1 : P.fp.rt.L.toSum.T.par.W (aS6 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) m =
      OnBytes.Road.Hd.place Wd.slot
        (P.fp.rt.L.toSum.T.par.vars (aS6 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)) p6.first)
    (D2 : P.fp.rt.L.toSum.T.par.inc (aS6 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) m =
      gl.val p6.target - p6.start.value gl Wd) :
    hd2.row.value gl Wd = 0 ↔
      Blocks.Form.val (Sum.elim m w)
        (prodU (J₂ := J₂) P.fp.rt.L (aD6 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7).out) = 0 := by
  subst hp6
  exact level_row_stg (J₂ := J₂) W.w6.num Ld.c6 Ld.s3' nz.b6
    (aS6 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) g7.t6 rfl ht6 f6
    (F₀_ok _ (P.fp.rt.L.eq0 : Eq0 P.fp.rt.L.toSum.T.par)) Ex y Wd m D1 D2
    (fun _ _ => Finset.sum_eq_zero fun b _ => (show Empty from b).elim) false true h0 h1
    (fun z vals => by
      show ([(1 : Cb.Gl.E) * [vals false, vals true].prod]).sum = _
      simp)
    (fun _ b => Empty.elim b) (fun _ _ b _ => Empty.elim b) w

/-- **The squares' layer's own claim**, at the first sub-proof's letters. -/
theorem sqF_of_led (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (nz : NzT (tailW P) (ksOf Pp hp) (t0.drop (k0 g)))
    (x : P.ofp.fs.X3) (g7 : Tg7) {p1 : OnBytes.Model.Psc}
    (hp1 : p1 = (levelRec Pp.rd.muV
      (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).2
      (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).1
      (orderDefault Pp.rd.muV) F4 ((ksOf Pp hp).tc1 (t0.drop (k0 g)))))
    (ht1 : g7.t1 = p1.target)
    (f1 : StgFits gl (tailW P).s1 (aS1 (tailW P) (ksOf Pp hp) (t0.drop (k0 g)) x)
      (levelWs Pp.rd.muV
        (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).2
        (orderDefault Pp.rd.muV)) Pp.rd.muV 2)
    (h0 : W.w1.num false = 0) (h1 : W.w1.num true = 1) (Ex : ExtSpec) (y : Ex.Str)
    (Wd : World Cb.Gl.E) (m : P.nr.J → Cb.Gl.E) (w : J₂ → Cb.Gl.E)
    (D1 : P.nr.sq.R.L.toSum.T.par.W (aS1 (tailW P) (ksOf Pp hp) (t0.drop (k0 g)) x) m =
      OnBytes.Road.Hd.place Wd.slot
        (P.nr.sq.R.L.toSum.T.par.vars (aS1 (tailW P) (ksOf Pp hp) (t0.drop (k0 g)) x)) p1.first)
    (D2 : P.nr.sq.R.L.toSum.T.par.inc (aS1 (tailW P) (ksOf Pp hp) (t0.drop (k0 g)) x) m =
      gl.val p1.target - p1.start.value gl Wd) :
    H1.wpl.row.value gl Wd = 0 ↔
      Blocks.Form.val (Sum.elim m w)
        (u1At (J₂ := J₂) P.nr (aD1 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7).out) = 0 := by
  subst hp1
  obtain ⟨v1, c1⟩ := Ld.c1
  exact level_row_stgUp (J₂ := J₂) W.w1.num c1 Ld.s4 nz.b1
    (aS1 (tailW P) (ksOf Pp hp) (t0.drop (k0 g)) x) g7.t1 rfl ht1 f1
    (F₀_ok _ (P.nr.sq.R.L.eq0 : Eq0 P.nr.sq.R.L.toSum.T.par)) Ex y Wd m D1 D2
    (fun _ _ => Finset.sum_eq_zero fun b _ => (show Empty from b).elim) false true h0 h1
    (fun z vals => by
      show ([(1 : Cb.Gl.E) * [vals false, vals true].prod]).sum = _
      simp)
    (fun _ b _ _ => Empty.elim b) (fun _ _ b _ => Empty.elim b) w

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.pendingF_of_led
#print axioms OnBytes.Road.K4.mergeF_of_led
#print axioms OnBytes.Road.K4.gated5F_of_led
#print axioms OnBytes.Road.K4.gated6F_of_led
#print axioms OnBytes.Road.K4.sqF_of_led
