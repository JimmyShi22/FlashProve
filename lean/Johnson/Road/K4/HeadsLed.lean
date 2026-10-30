-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/HeadsLed.lean: THE PRODUCT LAYERS' OWN CLAIMS IN THE LIBRARY's LEDGER, AT A HEARING.
Under the record `Led7` of a hearing in a group that is not the first
(Johnson/Road/K4/OwnLedgers.lean), at the chain's data read off the hearing's tape with the states
`addsOf` (OnBytes/Desc/First/P1/TailAdds.lean): the row that K4's text holds for the squares' layer
(`H1.wpl.row`) and for the two gated layers (`o.hd.row`, `hd2.row`) is worth 0 exactly if the form
in which the library's ledger writes that layer's own claim is worth 0 at the stage's typed output:
`u1At` (Cb/Pv/Lay/End/NormsRows.lean) for the squares, `prodU` (Cb/Pv/Lay/End/RowForm.lean; the
first two members of `gatedLed`, End/GatedShare.lean) for the gated layers. Three statements and
their proofs.

NO NEW ARGUMENT: `level_row_stg`, `level_row_stgUp` (OwnRowsStage.lean) at `Led7.c1`, `c5`, `c6`;
(D3) and (D4) by unfolding the library's `ProdL`.

Limits. All letters are the caller's. PREMISES: `Led7`; `StgFits` at the stage (fitsAt1, fitsAt5,
fitsAt6 of StageOuts.lean give it); the stage's target; that the two end values are numbered 0 and
1; (D1), (D2) at the stage's state in the world Wd. A group that is not the first. One world: no
draw. Nothing on the layers' other claims. Nothing on soundness.
-/
import Johnson.Road.K4.OwnRowsStage
import Johnson.Road.K4.StageOuts
import Cb.Pv.Lay.End.NormsRows

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
open OnBytes.Desc.First.P1 (gl NzT TailM TailR Tg7 aD1 aS1 aD5 aS5 aD6 aS6 drawnOf levelRec levelWs)
open Inst.Model (Scl)

variable [scl : Scl] {M Xs : Type} (P : FullPar Cb.Gl.E M Xs) {R : TailR}
  (W : TailM P.own.toOwn.tail R) {Pp : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork} {J₂ : Type} [Fintype J₂]

/-- **The first gated layer's own claim.** -/
theorem gated5_of_led (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (nz : NzT P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1))
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7)
    (ht5 : g7.t5 = (levelRec Pp.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF)
      (OnBytes.Model.Aff.slot o.K.sH1) (orderRange Pp.rd.muH) G3
      ((ksOf Pp hp).tc5 (t0.drop 1))).target)
    (f5 : StgFits gl P.own.toOwn.tail.s5 (aS5 W (ksOf Pp hp) (t0.drop 1) nz x g7)
      (levelWs Pp.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF) (orderRange Pp.rd.muH))
      Pp.rd.muH 2)
    (h0 : W.w5.num false = 0) (h1 : W.w5.num true = 1) (Ex : ExtSpec) (y : Ex.Str)
    (Wd : World Cb.Gl.E) (m : P.fp.gp.J → Cb.Gl.E) (w : J₂ → Cb.Gl.E)
    (D1 : P.fp.gp.toSum.T.par.W (aS5 W (ksOf Pp hp) (t0.drop 1) nz x g7) m =
      OnBytes.Road.Hd.place Wd.slot
        (P.fp.gp.toSum.T.par.vars (aS5 W (ksOf Pp hp) (t0.drop 1) nz x g7))
        (levelRec Pp.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF)
          (OnBytes.Model.Aff.slot o.K.sH1) (orderRange Pp.rd.muH) G3
          ((ksOf Pp hp).tc5 (t0.drop 1))).first)
    (D2 : P.fp.gp.toSum.T.par.inc (aS5 W (ksOf Pp hp) (t0.drop 1) nz x g7) m =
      gl.val (levelRec Pp.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF)
          (OnBytes.Model.Aff.slot o.K.sH1) (orderRange Pp.rd.muH) G3
          ((ksOf Pp hp).tc5 (t0.drop 1))).target -
        (levelRec Pp.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF)
          (OnBytes.Model.Aff.slot o.K.sH1) (orderRange Pp.rd.muH) G3
          ((ksOf Pp hp).tc5 (t0.drop 1))).start.value gl Wd) :
    o.hd.row.value gl Wd = 0 ↔
      Blocks.Form.val (Sum.elim m w)
        (prodU (J₂ := J₂) P.fp.gp (aD5 W (ksOf Pp hp) (t0.drop 1) nz x g7).out) = 0 := by
  obtain ⟨v5, c5⟩ := Ld.c5
  exact level_row_stg (J₂ := J₂) W.w5.num c5 Ld.s3 nz.b5
    (aS5 W (ksOf Pp hp) (t0.drop 1) nz x g7) g7.t5 rfl ht5 f5
    (F₀_ok _ (P.fp.gp.eq0 : Eq0 P.fp.gp.toSum.T.par)) Ex y Wd m D1 D2
    (fun _ _ => Finset.sum_eq_zero fun b _ => (show Empty from b).elim) false true h0 h1
    (fun z vals => by
      show ([(1 : Cb.Gl.E) * [vals false, vals true].prod]).sum = _
      simp)
    (fun _ b => Empty.elim b) (fun _ _ b _ => Empty.elim b) w

/-- **The second gated layer's own claim.** -/
theorem gated6_of_led (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (nz : NzT P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1))
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7) {p6 : OnBytes.Model.Psc}
    (hp6 : p6 = (levelRec Pp.rd.muH2
      ((drawnOf ((((ksOf Pp hp).tc5 (t0.drop 1)).drop (Pp.rd.muH + 3)).drop 1)).toArray ++
        downFrom o.K.rs Pp.y.lfe ++ tT.r)
      (Road.Rows.start2 Pp.y.LamM o.K.sH1
        (drawnOf ((((ksOf Pp hp).tc5 (t0.drop 1)).drop (Pp.rd.muH + 3)).drop 1)).toArray)
      (orderRange Pp.rd.muH2) G3' ((ksOf Pp hp).tc6 (t0.drop 1))))
    (ht6 : g7.t6 = p6.target)
    (f6 : StgFits gl P.own.toOwn.tail.s6 (aS6 W (ksOf Pp hp) (t0.drop 1) nz x g7)
      (levelWs Pp.rd.muH2
        ((drawnOf ((((ksOf Pp hp).tc5 (t0.drop 1)).drop (Pp.rd.muH + 3)).drop 1)).toArray ++
          downFrom o.K.rs Pp.y.lfe ++ tT.r) (orderRange Pp.rd.muH2)) Pp.rd.muH2 2)
    (h0 : W.w6.num false = 0) (h1 : W.w6.num true = 1) (Ex : ExtSpec) (y : Ex.Str)
    (Wd : World Cb.Gl.E) (m : P.fp.rt.L.J → Cb.Gl.E) (w : J₂ → Cb.Gl.E)
    (D1 : P.fp.rt.L.toSum.T.par.W (aS6 W (ksOf Pp hp) (t0.drop 1) nz x g7) m =
      OnBytes.Road.Hd.place Wd.slot
        (P.fp.rt.L.toSum.T.par.vars (aS6 W (ksOf Pp hp) (t0.drop 1) nz x g7)) p6.first)
    (D2 : P.fp.rt.L.toSum.T.par.inc (aS6 W (ksOf Pp hp) (t0.drop 1) nz x g7) m =
      gl.val p6.target - p6.start.value gl Wd) :
    hd2.row.value gl Wd = 0 ↔
      Blocks.Form.val (Sum.elim m w)
        (prodU (J₂ := J₂) P.fp.rt.L (aD6 W (ksOf Pp hp) (t0.drop 1) nz x g7).out) = 0 := by
  subst hp6
  exact level_row_stg (J₂ := J₂) W.w6.num Ld.c6 Ld.s3' nz.b6
    (aS6 W (ksOf Pp hp) (t0.drop 1) nz x g7) g7.t6 rfl ht6 f6
    (F₀_ok _ (P.fp.rt.L.eq0 : Eq0 P.fp.rt.L.toSum.T.par)) Ex y Wd m D1 D2
    (fun _ _ => Finset.sum_eq_zero fun b _ => (show Empty from b).elim) false true h0 h1
    (fun z vals => by
      show ([(1 : Cb.Gl.E) * [vals false, vals true].prod]).sum = _
      simp)
    (fun _ b => Empty.elim b) (fun _ _ b _ => Empty.elim b) w

/-- **The squares' layer's own claim.** -/
theorem sq_of_led (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (nz : NzT P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1))
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7) {p1 : OnBytes.Model.Psc}
    (hp1 : p1 = (levelRec Pp.rd.muV
      (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).2
      (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).1
      (orderDefault Pp.rd.muV) F4 ((ksOf Pp hp).tc1 (t0.drop 1))))
    (ht1 : g7.t1 = p1.target)
    (f1 : StgFits gl P.own.toOwn.tail.s1 (aS1 P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1) x)
      (levelWs Pp.rd.muV
        (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).2
        (orderDefault Pp.rd.muV)) Pp.rd.muV 2)
    (h0 : W.w1.num false = 0) (h1 : W.w1.num true = 1) (Ex : ExtSpec) (y : Ex.Str)
    (Wd : World Cb.Gl.E) (m : P.nr.J → Cb.Gl.E) (w : J₂ → Cb.Gl.E)
    (D1 : P.nr.sq.R.L.toSum.T.par.W (aS1 P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1) x) m =
      OnBytes.Road.Hd.place Wd.slot
        (P.nr.sq.R.L.toSum.T.par.vars (aS1 P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1) x)) p1.first)
    (D2 : P.nr.sq.R.L.toSum.T.par.inc (aS1 P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1) x) m =
      gl.val p1.target - p1.start.value gl Wd) :
    H1.wpl.row.value gl Wd = 0 ↔
      Blocks.Form.val (Sum.elim m w)
        (u1At (J₂ := J₂) P.nr (aD1 W (ksOf Pp hp) (t0.drop 1) nz x g7).out) = 0 := by
  subst hp1
  obtain ⟨v1, c1⟩ := Ld.c1
  exact level_row_stgUp (J₂ := J₂) W.w1.num c1 Ld.s4 nz.b1
    (aS1 P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1) x) g7.t1 rfl ht1 f1
    (F₀_ok _ (P.nr.sq.R.L.eq0 : Eq0 P.nr.sq.R.L.toSum.T.par)) Ex y Wd m D1 D2
    (fun _ _ => Finset.sum_eq_zero fun b _ => (show Empty from b).elim) false true h0 h1
    (fun z vals => by
      show ([(1 : Cb.Gl.E) * [vals false, vals true].prod]).sum = _
      simp)
    (fun _ b _ _ => Empty.elim b) (fun _ _ b _ => Empty.elim b) w

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.gated5_of_led
#print axioms OnBytes.Road.K4.gated6_of_led
#print axioms OnBytes.Road.K4.sq_of_led
