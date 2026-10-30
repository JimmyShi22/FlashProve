-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/RowsLed.lean: THE PRODUCT LAYERS' AND THE MERGE's OWN CLAIMS AT A HEARING, GATHERED.
Under the record `Led7` of a hearing in a group that is not the first
(Johnson/Road/K4/OwnLedgers.lean) and the targets `TgRec` (ClaimsHeard.lean): if the three rows that
K4's text holds for its product layers are worth 0 in the world of a ledger later than the hearing's
last, the three forms in which the library's ledger writes these layers' own claims are worth 0 at
the stages' typed outputs; and if the form that K4's run "back" makes as the merge's own claim is
worth 0 in the world of a ledger later than that run's, the merge's part of the library's ledger
holds. (D1) to (D4) are paid inside; what stays are ties of entries to mask entries and the typed
halves of (D2). One lemma and two statements, with proofs.

  `fmt_of_fits`: a stage's typed format, from its maps' data (`StgM`, `StgM.Ok`) and `StgFits`.
  `rows_of_led`: `u1At P.nr (aD1 …).out`, `prodU P.fp.gp (aD5 …).out` and `prodU P.fp.rt.L (aD6
    …).out` are worth 0 at `Sum.elim m w`.
  `merge_row_of_led`: `Ledger.Holds (mergeLed P.wp0 ((k4Tail …).z7 x).2) (Sum.elim m w)`.

NO NEW ARGUMENT: `sq_of_led`, `gated5_of_led`, `gated6_of_led` (HeadsLed.lean), `merge_of_led`
(MergeLed.lean), `level_d1`, `level_d2`, `merge_d1`, `merge_d2` (OwnD12Calls.lean), `fits7`
(StageFitsRest.lean), `Led7`'s fields on sizes and later ledgers.

Limits. All letters are the caller's. PREMISES: `Led7`; `TgRec`; `TailM.Ok`; `StgFits` at the stages
1, 5, 6 (fitsAt1, fitsAt5, fitsAt6 of StageOuts.lean); hk; the numbers of the end values; the
ledgers later; `Sized Fb`; hw1, hw5, hw6, hw7: WHICH ENTRY SERVES AS WHICH COEFFICIENT OF A HIDING
POLYNOMIAL, at the records' own first slots; hinc1, hinc5, hinc6, hinc7: THE TYPED HALVES OF (D2)
(IncsHeard.lean, IncsOut.lean conclude them); that the rows are worth 0. One direction. A group that
is not the first. One world each: no draw. The row products' and the batched sumcheck's own claims
are not spoken of. Nothing on soundness.
-/
import Johnson.Road.K4.HeadsLed
import Johnson.Road.K4.MergeLed
import Johnson.Road.K4.OwnD12Calls
import Johnson.Road.K4.ClaimsHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb TWhole Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model (Fork Forest.Heard Level Tsc World Aff orderDefault orderRange wsForkStart
    powers)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard downFrom normsStart)
open OnBytes.Tie.Pv (slotP)
open OnBytes.Tie.Pv.Lay (StgFits)
open OnBytes.Desc.First.P1 (gl NzT TailM TailR StgM ScR Tg7 addsOf aD1 aS1 aD5 aS5 aD6 aS6 aS7
  drawnOf levelRec levelWs tapeEps)
open OnBytes.Slice (GE)
open Inst.Model (Scl)

/-- A stage's typed format. -/
theorem fmt_of_fits {M X : Type} {S : Stg GE M X} {r : ScR} (Wm : StgM S r) (ok : Wm.Ok)
    {st : S.L.St} {ws : List OnBytes.Psc.Weight} {k dY : ℕ} (f : StgFits gl S st ws k dY) :
    S.L.T.par.fmt = List.replicate k (pfCube GE 2) ++ [pDummy GE dY] := by
  rw [Wm.hf, ok.k, f.k, ok.dy, f.dY]

variable [scl : Scl] {M Xs : Type} (P : FullPar Cb.Gl.E M Xs) {R : TailR}
  (W : TailM P.own.toOwn.tail R) {Pp : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork} {J₂ : Type} [Fintype J₂]

/-- **The three product layers' own claims, from the rows' zeros.** -/
theorem rows_of_led (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (nz : NzT P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1))
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7)
    (T : TgRec g7 Pp hp o t0 H1 tT F4 G2 G3 G3') (ok : W.Ok)
    (f1 : StgFits gl P.own.toOwn.tail.s1 (aS1 P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1) x)
      (levelWs Pp.rd.muV
        (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).2
        (orderDefault Pp.rd.muV)) Pp.rd.muV 2)
    (f5 : StgFits gl P.own.toOwn.tail.s5 (aS5 W (ksOf Pp hp) (t0.drop 1) nz x g7)
      (levelWs Pp.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF) (orderRange Pp.rd.muH))
      Pp.rd.muH 2)
    (f6 : StgFits gl P.own.toOwn.tail.s6 (aS6 W (ksOf Pp hp) (t0.drop 1) nz x g7)
      (levelWs Pp.rd.muH2
        ((drawnOf ((((ksOf Pp hp).tc5 (t0.drop 1)).drop (Pp.rd.muH + 3)).drop 1)).toArray ++
          downFrom o.K.rs Pp.y.lfe ++ tT.r) (orderRange Pp.rd.muH2)) Pp.rd.muH2 2)
    (n10 : W.w1.num false = 0) (n11 : W.w1.num true = 1) (n50 : W.w5.num false = 0)
    (n51 : W.w5.num true = 1) (n60 : W.w6.num false = 0) (n61 : W.w6.num true = 1)
    (Ex : ExtSpec) (y : Ex.Str) {Hl : Fork} (hL : Fo.Later G Hl) (mask : ℕ → Cb.Gl.E)
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (m : P.nr.J → Cb.Gl.E) (w : J₂ → Cb.Gl.E)
    (hw1 : ∀ q, m (P.nr.sq.R.L.toSum.T.par.wAt q) =
      mask (slotP P.nr.sq.R.L.toSum.T.par.fmt (levelRec Pp.rd.muV
      (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).2
      (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).1
      (orderDefault Pp.rd.muV) F4 ((ksOf Pp hp).tc1 (t0.drop 1))).first q))
    (hw5 : ∀ q, m (P.fp.gp.toSum.T.par.wAt q) =
      mask (slotP P.fp.gp.toSum.T.par.fmt (levelRec Pp.rd.muH (downFrom o.K.rs o.K.fin.wD ++
          o.H.ztF)
      (OnBytes.Model.Aff.slot o.K.sH1) (orderRange Pp.rd.muH) G3 ((ksOf Pp hp).tc5 (t0.drop
          1))).first q))
    (hw6 : ∀ q, m (P.fp.rt.L.toSum.T.par.wAt q) =
      mask (slotP P.fp.rt.L.toSum.T.par.fmt (levelRec Pp.rd.muH2
      ((drawnOf ((((ksOf Pp hp).tc5 (t0.drop 1)).drop (Pp.rd.muH + 3)).drop 1)).toArray ++
        downFrom o.K.rs Pp.y.lfe ++ tT.r)
      (Road.Rows.start2 Pp.y.LamM o.K.sH1
        (drawnOf ((((ksOf Pp hp).tc5 (t0.drop 1)).drop (Pp.rd.muH + 3)).drop 1)).toArray)
      (orderRange Pp.rd.muH2) G3' ((ksOf Pp hp).tc6 (t0.drop 1))).first q))
    (hinc1 : P.nr.sq.R.L.toSum.T.par.inc (aS1 P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1) x) m =
      maskSum Hl
          (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).1 mask -
        entSum (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop 1).drop 1)).toArray H1.PV).1
          entry)
    (hinc5 : P.fp.gp.toSum.T.par.inc (aS5 W (ksOf Pp hp) (t0.drop 1) nz x g7) m =
      maskSum Hl (Aff.slot o.K.sH1) mask - entSum (Aff.slot o.K.sH1) entry)
    (hinc6 : P.fp.rt.L.toSum.T.par.inc (aS6 W (ksOf Pp hp) (t0.drop 1) nz x g7) m =
      maskSum Hl (Road.Rows.start2 Pp.y.LamM o.K.sH1
          (drawnOf ((((ksOf Pp hp).tc5 (t0.drop 1)).drop (Pp.rd.muH + 3)).drop 1)).toArray) mask -
        entSum (Road.Rows.start2 Pp.y.LamM o.K.sH1
          (drawnOf ((((ksOf Pp hp).tc5 (t0.drop 1)).drop (Pp.rd.muH + 3)).drop 1)).toArray) entry)
    (z1 : H1.wpl.row.value gl (Hl.worldOf gl mask entry) = 0)
    (z5 : o.hd.row.value gl (Hl.worldOf gl mask entry) = 0)
    (z6 : hd2.row.value gl (Hl.worldOf gl mask entry) = 0) :
    Blocks.Form.val (Sum.elim m w)
        (u1At (J₂ := J₂) P.nr (aD1 W (ksOf Pp hp) (t0.drop 1) nz x g7).out) = 0 ∧
      Blocks.Form.val (Sum.elim m w)
        (prodU (J₂ := J₂) P.fp.gp (aD5 W (ksOf Pp hp) (t0.drop 1) nz x g7).out) = 0 ∧
      Blocks.Form.val (Sum.elim m w)
        (prodU (J₂ := J₂) P.fp.rt.L (aD6 W (ksOf Pp hp) (t0.drop 1) nz x g7).out) = 0 := by
  obtain ⟨v1, c1⟩ := Ld.c1
  obtain ⟨v5, c5⟩ := Ld.c5
  have A1 := level_d1 P.nr.sq.R.L.toSum.T.par (aS1 P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1) x) c1
    Ld.s4 (fmt_of_fits W.w1 ok.s1 f1) (Ld.g7.trans hL) mask entry m hw1
  have B1 := level_d2 P.nr.sq.R.L.toSum.T.par (aS1 P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1) x) c1
    Ld.s4 (Ld.g7.trans hL) mask entry m hinc1
  have A5 := level_d1 P.fp.gp.toSum.T.par (aS5 W (ksOf Pp hp) (t0.drop 1) nz x g7) c5 Ld.s3
    (fmt_of_fits W.w5 ok.s5 f5) (Ld.g3'.trans hL) mask entry m hw5
  have B5 := level_d2 P.fp.gp.toSum.T.par (aS5 W (ksOf Pp hp) (t0.drop 1) nz x g7) c5 Ld.s3
    (Ld.g3'.trans hL) mask entry m hinc5
  have A6 := level_d1 P.fp.rt.L.toSum.T.par (aS6 W (ksOf Pp hp) (t0.drop 1) nz x g7) Ld.c6 Ld.s3'
    (fmt_of_fits W.w6 ok.s6 f6) (Ld.g4.trans hL) mask entry m hw6
  have B6 := level_d2 P.fp.rt.L.toSum.T.par (aS6 W (ksOf Pp hp) (t0.drop 1) nz x g7) Ld.c6 Ld.s3'
    (Ld.g4.trans hL) mask entry m hinc6
  exact ⟨(sq_of_led P W Ld nz x g7 rfl T.t1 f1 n10 n11 Ex y _ m w A1 B1).1 z1,
    (gated5_of_led P W Ld nz x g7 T.t5 f5 n50 n51 Ex y _ m w A5 B5).1 z5,
    (gated6_of_led P W Ld nz x g7 rfl T.t6 f6 n60 n61 Ex y _ m w A6 B6).1 z6⟩

/-- **The merge's part of the ledger, from its own claim's zero.** Fb: the ledger from which the run
"back" makes the merge's own claim; Fb': the ledger behind it. -/
theorem merge_row_of_led (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (nz : NzT P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1))
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7)
    (T : TgRec g7 Pp hp o t0 H1 tT F4 G2 G3 G3') (ok : W.Ok)
    (hk : P.own.toOwn.tail.s7.L.S.k = Pp.wsLay.lk) (n7 : W.w7.num () = 0) (Ex : ExtSpec)
    (y : Ex.Str) {Fb Fb' H2 : Fork} {rowM : Aff}
    (hc : ownClaim o.wo.p o.wo.fvp {} Fb = some (rowM, Fb'))
    (hsb : OnBytes.PscRun.Sized Fb)
    (hLb : Fo.Later Fb' H2) (hL4 : Fo.Later G4 H2) (mask : ℕ → Cb.Gl.E)
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (m : P.wp0.J → Cb.Gl.E) (w : J₂ → Cb.Gl.E)
    (hw7 : ∀ q, m (P.wp0.wt.L.toSum.T.par.wAt q) =
      mask (slotP P.wp0.wt.L.toSum.T.par.fmt o.wo.p.first q))
    (hinc7 : P.wp0.wt.L.toSum.T.par.inc (aS7 W (ksOf Pp hp) (t0.drop 1) nz x g7) m =
      maskSum H2 (wsForkStart ((Array.range (hp.NCL - 0)).map (o.K.sV + ·) ++ #[])
          (powers (tapeEps ((ksOf Pp hp).tcW (t0.drop 1)))
            ((Array.range (hp.NCL - 0)).map (o.K.sV + ·) ++ #[]).size)) mask -
        entSum (wsForkStart ((Array.range (hp.NCL - 0)).map (o.K.sV + ·) ++ #[])
          (powers (tapeEps ((ksOf Pp hp).tcW (t0.drop 1)))
            ((Array.range (hp.NCL - 0)).map (o.K.sV + ·) ++ #[]).size)) entry)
    (z : rowM.value gl (H2.worldOf gl mask entry) = 0) :
    TWhole.Ledger.Holds
      (mergeLed (J₂ := J₂) P.wp0
        ((k4Tail W Pp hp t0 nz (addsOf W (ksOf Pp hp) (t0.drop 1) nz x g7)).z7 x).2)
      (Sum.elim m w) := by
  obtain ⟨cl, c7⟩ := Ld.c7
  obtain ⟨er, D1⟩ := merge_d1 P.wp0.wt.L.toSum.T.par (aS7 W (ksOf Pp hp) (t0.drop 1) nz x g7) c7 hc
    hsb (fmt_of_fits W.w7 ok.s7 (fits7 P (aS7 W (ksOf Pp hp) (t0.drop 1) nz x g7) Pp.wsLay.lk hk))
    hLb mask entry m hw7
  have D2 := merge_d2 P.wp0.wt.L.toSum.T.par (aS7 W (ksOf Pp hp) (t0.drop 1) nz x g7) c7 hL4 mask
    entry m hinc7
  rw [er] at z
  exact (merge_of_led P W Ld hk nz x g7 T.t7 n7 Ex y _ m w D1 D2).1 z

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.fmt_of_fits
#print axioms OnBytes.Road.K4.rows_of_led
#print axioms OnBytes.Road.K4.merge_row_of_led
