-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SixLedFirst.lean: THE FIRST GROUP's TWIN OF SixLed.lean: THE FIVE OWN CLAIMS AND THE
MERGE's PART OF THE LIBRARY's LEDGER, AT A HEARING, FROM THE TWO RUNS OF CLAIMS. Under the record
`LedG` of a hearing of the layers' own rounds in any group (Johnson/Road/K4/OwnLedgersG.lean), the
targets `TgRecF` (ClaimsHeardFirst.lean), at the letters `tailW P` of the first sub-proof's chain
behind its three points (Cb/Pv/Lay/End/FirstShare.lean) and the tape behind the points in front
(`t0.drop (k0 g)`), and K4's two runs of claims (`formsFrontWith`, `formsBack`,
OnBytes/Desc/First/K4/Plain.lean) from a ledger later than the hearing's last: if every form of the
first list is worth 0 in the world of the ledger behind the first run, and every form of the second
in the world of the ledger behind the second, with one mask row and one table of entries: then the
forms in which the library's ledger writes the own claims of the squares' layer, the row products'
sumcheck, the two gated layers and the batched sumcheck are worth 0 at the stages' typed outputs,
and the merge's part of the ledger (`mergeLedF`, Cb/Pv/Lay/End/MergeShare.lean) holds. Two records
of premises and three statements with proofs.

  `HwTiesF`: which entry serves as which coefficient of a hiding polynomial, at the seven stages'
    typed sumchecks: the record `HwTies` (HwTies.lean) at these letters; the seventh at `V.wf.L`.
  `IncTiesF`: the typed halves of (D2) at the stages 1, 2, 5, 6 in the first run's ledger, at 7 in
    the second's, and (D2) itself at the stage 4 in the second's. The seventh's start form runs over
    `mergeSlots hp g o` (OnBytes/Desc/First/K4/MergeClaims.lean): in the first group one claim of
    the batched sumcheck fewer, and the embedding's slot last.
  `u2_atF`, `u4_atF`: the row products' and the batched sumcheck's own claims, (D1) and (D2) paid
    from `HwTiesF`'s and `IncTiesF`'s sentences.
  `six_of_ledF`: all six.

NO NEW ARGUMENT: SixLed.lean's proofs turned to these letters by program, over `rows_of_ledF`,
`merge_row_of_ledF` (RowsLedFirst.lean), `u2_of_ledF` (TokRowFirst.lean), `u4_of_ledF`
(StackRowFirst.lean); `runs_later` (SixLed.lean), `front_rows`, `back_rows` (RowsMembers.lean),
`d1_ended_at` (OwnD12Calls.lean), `tsc_d2` (KtLed.lean) speak of no group and are taken as they
stand. By hand: the two records' seventh fields, f7 in the place of hk, `LedG.g5` in the place of
`Led7.g4`, `mergeLedF`.

Limits. All letters are the caller's. WHAT STAYS A NAMED PREMISE: `LedG` · `NzT` (no further
challenge reads 0) · `TgRecF` · `TailM.Ok` · `NumTiesF` and n7 (the numbers of the end values) ·
`StgFits` at the stages 1, 2, 4, 5, 6, 7 · `HwTiesF` at the seven records' first slots and
`IncTiesF`: NEITHER IS SHOWN OF ANY VALUE HERE; the field h7's start form is the one place where the
embedding's slot is named · hNI, hNP, hNO, hst2 (as `u2_of_ledF` asks them) · hD4 ((D4) at the stage
4, as `u4_of_ledF` asks it) · F0 later than G, with arrays of the right sizes · the two runs and
their forms' zeros. One direction. THE GROUP g IS A LETTER: nothing here says that it is the first;
the typed letters are the first sub-proof's. One mask row, one table of entries, one m: no draw. The
typed outputs are written in two ways, `(aD1 ...).out` and `((tailW P).b2 (... .z7 x)).2`, as the
lemmas beneath write them. Nothing on the pending row (HeadsLedFirst.lean), on the embedding's own
claim, on the two further points in front. Nothing on soundness.
-/
import Johnson.Road.K4.SixLed
import Johnson.Road.K4.RowsLedFirst
import Johnson.Road.K4.TokRowFirst
import Johnson.Road.K4.StackRowFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb TWhole Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model (Fork Forest.Heard Level Tsc World Aff orderDefault orderRange wsForkStart
  powers ledNP ledNO)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard downFrom normsStart)
open OnBytes.Tie.Pv (slotP)
open OnBytes.Tie.Pv.Lay (StgFits)
open OnBytes.PscRun (hideRun_ok)
open OnBytes.Desc.First.P1 (gl NzT TailM TailR Tg7 tailT addsOf aD1 aS1 aD2 aS2 aD4 aS4 aD5 aS5 aD6
  aS6 aS7 drawnOf levelRec levelWs tscWs plainWs tapeEps tscIn_heard)
open OnBytes.Slice (GE)
open Inst.Model (Scl)

variable [scl : Scl] {M Xs : Type} (P : FullFPar Cb.Gl.E M Xs) {R : TailR}
  (W : TailM (tailW P) R) {Pp : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own}
  {F G : Fork} {t0 u u5 : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {J₂ : Type} [Fintype J₂]

/-- Which entry serves as which coefficient of a hiding polynomial: the seven equations, at the
stages' typed sumchecks: `HwTies` (HwTies.lean) at the first sub-proof's letters; the seventh is
said of `V.wf.L`. A record of premises. -/
structure HwTiesF (V : FullFPar Cb.Gl.E M Xs) (m : V.J → Cb.Gl.E) (mask : ℕ → Cb.Gl.E)
    (f1 f2 f3 f4 f5 f6 f7 : ℕ) : Prop where
  hw1 : ∀ q, m (V.nr.sq.R.L.toSum.T.par.wAt q) = mask (slotP V.nr.sq.R.L.toSum.T.par.fmt f1 q)
  hw2 : ∀ q, m ((tailW V).s2.L.T.par.wAt q) = mask (slotP (tailW V).s2.L.T.par.fmt f2 q)
  hw3 : ∀ q, m ((tailW V).s3.L.T.par.wAt q) = mask (slotP (tailW V).s3.L.T.par.fmt f3 q)
  hw4 : ∀ q, m (V.ip.inn.toSum.T.par.wAt q) = mask (slotP V.ip.inn.toSum.T.par.fmt f4 q)
  hw5 : ∀ q, m (V.fp.gp.toSum.T.par.wAt q) = mask (slotP V.fp.gp.toSum.T.par.fmt f5 q)
  hw6 : ∀ q, m (V.fp.rt.L.toSum.T.par.wAt q) = mask (slotP V.fp.rt.L.toSum.T.par.fmt f6 q)
  hw7 : ∀ q, m (V.wf.L.toSum.T.par.wAt q) = mask (slotP V.wf.L.toSum.T.par.fmt f7 q)

/-- The typed halves of (D2), and (D2) at the batched sumcheck. Fl: the ledger behind the run
"front"; Fm: the one behind the run "back". -/
structure IncTiesF (Pp : Pub) (hp : HPlan2) (g : ℕ) (o : Own) (t0 : Tape) (H1 : Heard) (G2 : Fork)
    (nz : NzT (tailW P) (ksOf Pp hp) (t0.drop (k0 g)))
    (x : P.ofp.fs.X3) (g7 : Tg7) (Fl Fm : Fork) (mask : ℕ → Cb.Gl.E)
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (m : P.J → Cb.Gl.E) : Prop where
  h1 : P.nr.sq.R.L.toSum.T.par.inc (aS1 (tailW P) (ksOf Pp hp) (t0.drop (k0 g)) x) m =
    maskSum Fl (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).1
        mask -
      entSum (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).1
        entry
  h2 : (tailW P).s2.L.T.par.inc (aS2 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) m =
    maskSum Fl (Aff.slot H1.tV.sCl) mask - entSum (Aff.slot H1.tV.sCl) entry
  d4 : (tailW P).s4.L.T.par.inc (aS4 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) m =
    gl.val g7.t4 - (stackStart o.v o.H G2 ((ksOf Pp hp).tc4 (t0.drop (k0 g)))).value gl
      (Fm.worldOf gl mask entry)
  h5 : P.fp.gp.toSum.T.par.inc (aS5 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) m =
    maskSum Fl (Aff.slot o.K.sH1) mask - entSum (Aff.slot o.K.sH1) entry
  h6 : P.fp.rt.L.toSum.T.par.inc (aS6 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) m =
    maskSum Fl (Road.Rows.start2 Pp.y.LamM o.K.sH1
        (drawnOf ((((ksOf Pp hp).tc5 (t0.drop (k0 g))).drop (Pp.rd.muH + 3)).drop 1)).toArray)
        mask -
      entSum (Road.Rows.start2 Pp.y.LamM o.K.sH1
        (drawnOf ((((ksOf Pp hp).tc5 (t0.drop (k0 g))).drop (Pp.rd.muH + 3)).drop 1)).toArray)
        entry
  h7 : P.wf.L.toSum.T.par.inc (aS7 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) m =
    maskSum Fm (wsForkStart (mergeSlots hp g o)
        (powers (tapeEps ((ksOf Pp hp).tcW (t0.drop (k0 g)))) (mergeSlots hp g o).size)) mask -
      entSum (wsForkStart (mergeSlots hp g o)
        (powers (tapeEps ((ksOf Pp hp).tcW (t0.drop (k0 g)))) (mergeSlots hp g o).size)) entry

/-- **The row products' own claim**, (D1) and (D2) paid. -/
theorem u2_atF (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (nz : NzT (tailW P) (ksOf Pp hp) (t0.drop (k0 g)))
    (x : P.ofp.fs.X3) (g7 : Tg7) (ht2 : g7.t2 = H1.tV.p.target)
    (ok : W.Ok) (Nm : NumTiesF P W Pp.y.LamM) (hNI : Pp.y.NI = P.D.nNu)
    (hNP : ledNP Pp.y.h.xl = 7) (hNO : ledNO Pp.y.h.xl = 4)
    (hst2 : ((aS2 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7 : (tailW P).s2.L.St) :
      P.nr.rows.X2).2 = gl.val (tapeEps ((ksOf Pp hp).tcP (t0.drop (k0 g)))))
    (f2 : StgFits gl (tailW P).s2 (aS2 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
      (tscWs (H1.PV.toList.take Pp.y.h.lt)) Pp.y.h.lt 2)
    (hF2 : ∀ st, HFixs.OK _ ((tailW P).s2.F st)) (Ex : ExtSpec) (y : Ex.Str)
    {F0 Fl Fa : Fork} (l0 : Fo.Later G F0) (hS0 : OnBytes.PscRun.Sized F0) {rows : Bool}
    {fs1 : Array Aff} (hf : formsFrontWith rows Pp g o F0 = some (fs1, Fl))
    (ra : F0.hideRun o.H.tV.p.first (Array.replicate o.H.tV.p.walk.1.length zeroE)
      (subE zeroE oneE) = some Fa) (la : Fo.Later Fa Fl) (l1 : Fo.Later F0 Fl)
    (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E)
    (z1 : ∀ q ∈ fs1.toList, q.value gl (Fl.worldOf gl mask entry) = 0) (mm : M)
    (hw2 : ∀ q, P.msg mm ((tailW P).s2.L.T.par.wAt q) =
      mask (OnBytes.Tie.Pv.slotP (tailW P).s2.L.T.par.fmt H1.tV.p.first q))
    (hinc2 : (tailW P).s2.L.T.par.inc (aS2 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
        (P.msg mm) =
      maskSum Fl (Aff.slot H1.tV.sCl) mask - entSum (Aff.slot H1.tV.sCl) entry)
    (w : J₂ → Cb.Gl.E) :
    Blocks.Form.val (Sum.elim (P.msg mm) w)
      (u2At (J₂ := J₂) P.nr
        ((tailW P).b2 ((tailT W (ksOf Pp hp) (t0.drop (k0 g)) nz
            (addsOf W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)).z7 x)).2) = 0 := by
  obtain ⟨v2, c2⟩ := Ld.c2
  obtain ⟨C, τ, first, a⟩ := (tsc_recAt c2).psc
  have hlt := (tscIn_heard c2).1
  have hlen : (tscWs (H1.PV.toList.take Pp.y.h.lt)).length = Pp.y.h.lt := by
    unfold tscWs
    rw [List.length_map, List.length_take, Array.length_toList]
    exact Nat.min_eq_left hlt
  have hfmt : (tailW P).s2.L.T.par.fmt =
      List.replicate (tscWs (H1.PV.toList.take Pp.y.h.lt)).length (pfCube GE 2) ++
        [pDummy GE 2] := by
    rw [hlen, W.w2.hf, ok.s2.k, f2.k, ok.s2.dy, f2.dY]
  rw [Ld.kTV] at ra
  have D1 := d1_ended_at (tailW P).s2.L.T.par (aS2 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) a
    (fun w' hw' => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.1 hw'
      rfl) hfmt hS0 ra la mask entry (P.msg mm) hw2
  have D2 := tsc_d2 (tailW P).s2.L.T.par (aS2 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) c2 Ld.s8
    ((Ld.g1.trans l0).trans l1) mask entry (P.msg mm) hinc2
  exact u2_of_ledF P W Ld nz (addsOf W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) x Nm hNI hNP hNO hst2
    rfl ht2 f2 hF2 Ex y l0 hf (Fl.worldOf gl mask entry) z1 mm D1 D2 w

/-- **The batched sumcheck's own claim**, (D1) and (D2) paid. -/
theorem u4_atF (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (nz : NzT (tailW P) (ksOf Pp hp) (t0.drop (k0 g)))
    (x : P.ofp.fs.X3) (g7 : Tg7)
    (ht4 : g7.t4 = (stackRec o.v o.H hp.lamS G2 ((ksOf Pp hp).tc4 (t0.drop (k0 g)))).target)
    (ok : W.Ok)
    (hD4 : P.ip.inn.Sm.pol (aS4 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
        (P.ip.inn.Kp.outPt P.ip.inn.Mk
          ((tailW P).b4 ((tailT W (ksOf Pp hp) (t0.drop (k0 g)) nz
              (addsOf W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)).z7 x)).2)
        (tailT W (ksOf Pp hp) (t0.drop (k0 g)) nz
            (addsOf W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)).d4.v =
      gl.val (mulE o.K.fin.As o.K.fin.Bs))
    (f4 : StgFits gl (tailW P).s4 (aS4 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
      (plainWs hp.lamS) hp.lamS 2)
    (hF4 : ∀ st, HFixs.OK _ ((tailW P).s4.F st)) (Ex : ExtSpec) (y : Ex.Str) {Fm : Fork}
    (l2 : Fo.Later G Fm) (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E)
    (zS : o.K.rowS.value gl (Fm.worldOf gl mask entry) = 0) (mm : M)
    (hw4 : ∀ q, P.msg mm (P.ip.inn.toSum.T.par.wAt q) =
      mask (OnBytes.Tie.Pv.slotP P.ip.inn.toSum.T.par.fmt
        (stackRec o.v o.H hp.lamS G2 ((ksOf Pp hp).tc4 (t0.drop (k0 g)))).first q))
    (d24 : (tailW P).s4.L.T.par.inc (aS4 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) (P.msg mm) =
      gl.val g7.t4 - (stackStart o.v o.H G2 ((ksOf Pp hp).tc4 (t0.drop (k0 g)))).value gl
        (Fm.worldOf gl mask entry))
    (w : J₂ → Cb.Gl.E) :
    Blocks.Form.val (Sum.elim (P.msg mm) w)
      (upForm (J₂ := J₂) (Cb.Sub.formU P.ip.inn.toSum.T.par (fun _ b _ _ => PEmpty.elim b)
        ((tailW P).b4 ((tailT W (ksOf Pp hp) (t0.drop (k0 g)) nz
            (addsOf W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)).z7 x)).2)) = 0 := by
  have a := stack_ended Ld.c4
  obtain ⟨_, _, _, _, _, vals, Gx, _, _, hGx, hrow⟩ := stack_heard Ld.c4
  have hS2' : OnBytes.PscRun.Sized ({ G2 with next := G2.next + 1 + 2 * hp.lamS + 2 +
      (2 + (1 + Pp.y.LamM) + (hp.NCL - (if (g == 0) = true then 1 else 0))) } : Fork) := Ld.s2
  obtain ⟨_, hSx, _, _⟩ := hideRun_ok _ Gx _ _ _ hS2' hGx
  have hfmt : (tailW P).s4.L.T.par.fmt =
      List.replicate (plainWs hp.lamS).length (pfCube GE 2) ++ [pDummy GE 2] := by
    rw [show (plainWs hp.lamS).length = hp.lamS from List.length_replicate, W.w4.hf, ok.s4.k,
      f4.k, ok.s4.dy, f4.dY]
  have D1 := d1_ended_at (tailW P).s4.L.T.par (aS4 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) a
    (fun w' hw' => by
      rw [List.eq_of_mem_replicate hw']
      rfl) hfmt hSx hrow (Ld.g3.trans l2) mask entry (P.msg mm) hw4
  have D2 : (tailW P).s4.L.T.par.inc (aS4 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
      (P.msg mm) =
      gl.val (stackRec o.v o.H hp.lamS G2 ((ksOf Pp hp).tc4 (t0.drop (k0 g)))).target -
        (stackRec o.v o.H hp.lamS G2 ((ksOf Pp hp).tc4 (t0.drop (k0 g)))).start.value gl
          (Fm.worldOf gl mask entry) := by
    rw [a.start, ← ht4]
    exact d24
  exact u4_of_ledF P W Ld nz (addsOf W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) x hD4 rfl ht4 f4 hF4
    Ex y (Fm.worldOf gl mask entry) zS mm D1 D2 w

/-- **All six, from the two runs' zeros.** -/
theorem six_of_ledF (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (nz : NzT (tailW P) (ksOf Pp hp) (t0.drop (k0 g)))
    (x : P.ofp.fs.X3) (g7 : Tg7)
    (T : TgRecF g7 Pp hp g o t0 H1 tT F4 G2 G3 G3') (ok : W.Ok) (Nm : NumTiesF P W Pp.y.LamM)
    (n7 : W.w7.num () = 0)
    (f1 : StgFits gl (tailW P).s1 (aS1 (tailW P) (ksOf Pp hp) (t0.drop (k0 g)) x)
      (levelWs Pp.rd.muV
        (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).2
        (orderDefault Pp.rd.muV)) Pp.rd.muV 2)
    (f2 : StgFits gl (tailW P).s2 (aS2 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
      (tscWs (H1.PV.toList.take Pp.y.h.lt)) Pp.y.h.lt 2)
    (f4 : StgFits gl (tailW P).s4 (aS4 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
      (plainWs hp.lamS) hp.lamS 2)
    (f5 : StgFits gl (tailW P).s5 (aS5 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
      (levelWs Pp.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF) (orderRange Pp.rd.muH))
      Pp.rd.muH 2)
    (f6 : StgFits gl (tailW P).s6 (aS6 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
      (levelWs Pp.rd.muH2
        ((drawnOf ((((ksOf Pp hp).tc5 (t0.drop (k0 g))).drop (Pp.rd.muH + 3)).drop 1)).toArray ++
          downFrom o.K.rs Pp.y.lfe ++ tT.r) (orderRange Pp.rd.muH2)) Pp.rd.muH2 2)
    (f7 : StgFits gl (tailW P).s7 (aS7 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
      (plainWs Pp.wsLay.lk) Pp.wsLay.lk 1)
    (hNI : Pp.y.NI = P.D.nNu)
    (hNP : ledNP Pp.y.h.xl = 7) (hNO : ledNO Pp.y.h.xl = 4)
    (hst2 : ((aS2 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7 : (tailW P).s2.L.St) :
      P.nr.rows.X2).2 = gl.val (tapeEps ((ksOf Pp hp).tcP (t0.drop (k0 g)))))
    (hD4 : P.ip.inn.Sm.pol (aS4 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
        (P.ip.inn.Kp.outPt P.ip.inn.Mk
          ((tailW P).b4 ((tailT W (ksOf Pp hp) (t0.drop (k0 g)) nz
              (addsOf W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)).z7 x)).2)
        (tailT W (ksOf Pp hp) (t0.drop (k0 g)) nz
            (addsOf W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)).d4.v =
      gl.val (mulE o.K.fin.As o.K.fin.Bs))
    (Ex : ExtSpec) (y : Ex.Str) {F0 Fl Fm : Fork} (l0 : Fo.Later G F0)
    (hS0 : OnBytes.PscRun.Sized F0) {rows : Bool} {fs1 fs2 : Array Aff}
    (hf : formsFrontWith rows Pp g o F0 = some (fs1, Fl)) (hb : formsBack o Fl = some (fs2, Fm))
    (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E)
    (z1 : ∀ q ∈ fs1.toList, q.value gl (Fl.worldOf gl mask entry) = 0)
    (z2 : ∀ q ∈ fs2.toList, q.value gl (Fm.worldOf gl mask entry) = 0) (mm : M)
    (Hw : HwTiesF P (P.msg mm) mask
      (levelRec Pp.rd.muV
        (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).2
        (normsStart Pp.y H1.sW H1.gp (drawnOf ((t0.drop (k0 g)).drop 1)).toArray H1.PV).1
        (orderDefault Pp.rd.muV) F4 ((ksOf Pp hp).tc1 (t0.drop (k0 g)))).first
      H1.tV.p.first tT.p.first
      (stackRec o.v o.H hp.lamS G2 ((ksOf Pp hp).tc4 (t0.drop (k0 g)))).first
      (levelRec Pp.rd.muH (downFrom o.K.rs o.K.fin.wD ++ o.H.ztF) (Aff.slot o.K.sH1)
        (orderRange Pp.rd.muH) G3 ((ksOf Pp hp).tc5 (t0.drop (k0 g)))).first
      (levelRec Pp.rd.muH2
        ((drawnOf ((((ksOf Pp hp).tc5 (t0.drop (k0 g))).drop (Pp.rd.muH + 3)).drop 1)).toArray ++
          downFrom o.K.rs Pp.y.lfe ++ tT.r)
        (Road.Rows.start2 Pp.y.LamM o.K.sH1
          (drawnOf ((((ksOf Pp hp).tc5 (t0.drop (k0 g))).drop (Pp.rd.muH + 3)).drop 1)).toArray)
        (orderRange Pp.rd.muH2) G3' ((ksOf Pp hp).tc6 (t0.drop (k0 g)))).first
      o.wo.p.first)
    (I : IncTiesF P W Pp hp g o t0 H1 G2 nz x g7 Fl Fm mask entry (P.msg mm)) (w : J₂ → Cb.Gl.E) :
    Blocks.Form.val (Sum.elim (P.msg mm) w)
        (u1At (J₂ := J₂) P.nr (aD1 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7).out) = 0 ∧
      Blocks.Form.val (Sum.elim (P.msg mm) w)
        (u2At (J₂ := J₂) P.nr
          ((tailW P).b2 ((tailT W (ksOf Pp hp) (t0.drop (k0 g)) nz
              (addsOf W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)).z7 x)).2) = 0 ∧
      Blocks.Form.val (Sum.elim (P.msg mm) w)
        (prodU (J₂ := J₂) P.fp.gp (aD5 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7).out) = 0 ∧
      Blocks.Form.val (Sum.elim (P.msg mm) w)
        (prodU (J₂ := J₂) P.fp.rt.L (aD6 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7).out) = 0 ∧
      Blocks.Form.val (Sum.elim (P.msg mm) w)
        (upForm (J₂ := J₂) (Cb.Sub.formU P.ip.inn.toSum.T.par (fun _ b _ _ => PEmpty.elim b)
          ((tailW P).b4 ((tailT W (ksOf Pp hp) (t0.drop (k0 g)) nz
              (addsOf W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)).z7 x)).2)) = 0 ∧
      TWhole.Ledger.Holds
        (mergeLedF (J₂ := J₂) P.wp0 (tenEF P) (rhsF P) P.mkE
          ((tailT W (ksOf Pp hp) (t0.drop (k0 g)) nz
            (addsOf W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)).z7 x).2)
        (Sum.elim (P.msg mm) w) := by
  obtain ⟨l1, l12, hS1, Fa, ra, la⟩ := runs_later hS0 hf hb
  obtain ⟨m1, m5, m6, _⟩ := front_rows hf
  obtain ⟨mS, rowM, Fc, hc, mM, eM⟩ := back_rows hb
  have lG1 : Fo.Later G Fl := l0.trans l1
  have lG2 : Fo.Later G Fm := lG1.trans l12
  have zw : H1.wpl.row.value gl (Fl.worldOf gl mask entry) = 0 := by
    rw [← Ld.kWpl]
    exact z1 _ m1
  have lc : Fo.Later Fc Fm := by
    rw [eM]
    exact fo_paid_later _ _
  have R3 := rows_of_ledF (J₂ := J₂) P W Ld nz x g7 T ok f1 f5 f6 Nm.n1f Nm.n1t Nm.n5f Nm.n5t Nm.n6f
    Nm.n6t Ex y lG1 mask entry (P.msg mm) w Hw.hw1 Hw.hw5 Hw.hw6 I.h1 I.h5 I.h6 zw (z1 _ m5)
    (z1 _ (m6 hd2 Ld.eHd2))
  have U2 := u2_atF (J₂ := J₂) P W Ld nz x g7 T.t2 ok Nm hNI hNP hNO hst2 f2 P.nr.rows.tok.pick_ok
    Ex y l0 hS0 hf ra la l1 mask entry z1 mm Hw.hw2 I.h2 w
  have U4 := u4_atF (J₂ := J₂) P W Ld nz x g7 T.t4 ok hD4 f4 P.ip.inn.pick_okS Ex y lG2 mask entry
    (z2 _ mS) mm Hw.hw4 I.d4 w
  have Mg := merge_row_of_ledF (J₂ := J₂) P W Ld nz x g7 T ok f7 n7 Ex y hc hS1 lc
    (Ld.g5.trans lG2) mask entry (P.msg mm) w Hw.hw7 I.h7 (z2 _ mM)
  exact ⟨R3.1, U2, R3.2.1, R3.2.2, U4, Mg⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.u2_atF
#print axioms OnBytes.Road.K4.u4_atF
#print axioms OnBytes.Road.K4.six_of_ledF
