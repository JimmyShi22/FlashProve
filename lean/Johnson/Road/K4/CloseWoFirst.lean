-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/CloseWoFirst.lean: AT A YES OF THE PIECE THAT HOLDS K4's BLOCK, IN THE FIRST GROUP:
THE NAMED SENTENCE `WoSaysF` (Johnson/Road/K4/OwnAt.lean) OF THE HEARING's OWN MERGE RECORD, AT THE
SEVENTH STATE READ OFF THE TAPE, AGAINST THE ROW THAT `pendingRowO` RETURNS. The first group's twin
of CloseWo.lean. Four theorems. Glue: `woSaysF_at_ledG` (WoAtLedFirst.lean) with its premises on
sizes, numberings, outputs and the public record concluded under `Plan4F.MeetsF`, as
Johnson/Road/K4/SixKFirst.lean and CloseRowsFirst.lean do it for the own rows. No draw, no count.

  `pubAtWo_of_ledF`: under the premises of `pubAt_of_ledF` (PubAtFirst.lean): there is X with
    `PubAt` at LedG's own G2 and tc4, X.rd = Pp.rd and X.lk = lk. Bookkeeping over
    `pub34_of_hear_run` (PubOfHearTied.lean), which concludes both.
  `Plan4LF.wo_ledF`: at a hearing, at the first group's value with its slots and orders laid
    (`Plan4LF`), under `MeetsF` and the premises that `Plan4LF.wo_atF` concludes for it or asks
    itself (its binders): `WoSaysF` holds exactly if the row's sentence does.
  `Plan4LF.wo_atF`: the same at a yes, at every `LedG` and `TgRecF` of that hearing. The left side
    is typed after what the field wo of `Plan4LF.OwesF` (Johnson/Road/K4/CloseKFirst.lean)
    concludes: held by eye: that file is not imported.
  `Plan4LF.wo_atF_ref`: the same with (HE) concluded by `he_of_hear` (Johnson/Road/K4/WoEmbAt.lean),
    AT THE LIBRARY's REFERENCE PARAMETERS ALONE: in its place stand: the value's parameters are
    ppref, its number of column bits kRef, the public record's vocabulary ppref's; htok: the value's
    tokens at the first statement are the seat's array of tokens on the 2 ^ lT positions; `EmbNums`.
    The three sizes that `he_of_hear` asks are `MeetsF`'s own (hls, hB, dimIs).

THE ROW's SENTENCE: the sum over the cube's rows of `pendWeight gl r.g j` times the committed
matrix's row j read at the point `r.psi` turned round, plus the sum over the row's named mask
entries of the entry times its factor, is the reading of `r.target`.

Limits. PREMISES THAT STAY, in `Plan4LF.wo_atF`: `Plan4F.MeetsF` and pc.ds = dsFirst par · the yes ·
the ledger in front has arrays of the right sizes · `PubLines`, `LookLines`, the rotary tables' fit
· zOf and kTg at the first statement; the lookup's end form has filled slots alone · `ValueIs` (of
it the table of scales and the first layer are read), `ValueMoreF` (of it n4) · `LedG` and `TgRecF`
· (HE): THE ADDED PAIR `tenEF` AT THE CLAIMS' STATE AND THE EMBEDDING's CLAIM, whatever `claimE`
returns at what was heard, TAKE ONE VALUE AT THE MATRIX `starW` (concluded in `wo_atF_ref` alone) ·
hr: `pendingRowO` returns · hidx: the index masks' entry that the row names is the typed mask entry.
im, os, claims and S are letters: that a layers' link's end calls `pendingRowO` at the index masks'
number, the statement's messages, the plan's count and this record is not said here; nor that the
letter `Lt.wo` of the law gives such a row and its sentence. The cells are the value's `Wn` at the
message of part w: that another file's cells are these is not said. Nothing shows that these can be
met together. An equivalence of two sentences on numbers. Nothing on soundness.
-/
import Johnson.Road.K4.WoAtLedFirst
import Johnson.Road.K4.WoEmbAt
import Johnson.Road.K4.CloseWo
import Johnson.Road.K4.CloseRowsFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset
open TWhole Iop Cb Cb.Sub Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker OnBytes.Road OnBytes.Road.Rows
open OnBytes.Model (Reading Fork Forest.Heard Level Tsc WsShape WsClaim HTailF2)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.Desc.First.K4 (Par Seat hear engFl k0 envOf)
open OnBytes.Desc.First.P1 (gl NzT TailM Tg7 aS7 addsOf drawnOf tailT tailIsF_at)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.First.Pend (pendingRowO)
open Inst.Model (Scl Tables ppref)
open Inst.Model.Layout (kRef)
open Meaning.Emb (EmbNums)
open Inst.Model.FFSeg (Dim LW zpos)
open Cb.Pv.Lay.At (tval)

/-- **The public record at a hearing, with its reads' numbers and its number of column bits, in
`LedG`'s letters.** -/
theorem pubAtWo_of_ledF {Pp : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own}
    {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
    {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}
    (h : hear engFl Pp hp g fo F t0 = some (o, G, u))
    (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    {hS : OnBytes.Model.Layer.Shape} {pc : List (List String)} {D : Dim} {tb : Tables}
    {s : WsShape} {lk : ℕ} {s0 : OnBytes.Model.Forest.Shape} {tl : HTailF2}
    (B : PubLines Pp g hS pc D tb s lk s0 tl) (K : LookLines Pp fo s0)
    (Rp : ∀ (rt : Array E) (lam : ℕ), lam < Pp.y.Lam →
      RopeFits Reading.gl
        { v := o.v, wsLay := Pp.wsLay, rope := Pp.rope, rs := o.K.rs, rt := rt } D tb
        (g * Pp.y.Lam) lam)
    (hinv : ∀ tT, o.H.tT = some tT →
      Reading.gl.val (negE (invE tT.p.eps)) * Reading.gl.val tT.p.eps = -1) :
    ∃ X : Rows.Pub34 Cb.Gl.E,
      PubAt X Pp hp fo o G2 ((ksOf Pp hp).tc4 (t0.drop (k0 g))) D tb hS ∧ X.rd = Pp.rd ∧
        X.lk = lk := by
  obtain ⟨X, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, _, a13, a14, a15, a16, _, _, a19, a20,
    _, _, a23, a24, a25, a26, _, _, H1', G1x, G2x, _, _, u1x, u2x, _, n1, n2, _, hom, hst, hsh,
    _⟩ :=
    pub34_of_hear_run Reading.gl h B.hy B.S B.hs B.hg B.hrd B.hmats B.hρ B.Z B.hc B.hN B.hfl K.hsx
      K.hsy K.hzk K.he B.hs0 K.hpt B.Zw B.hsL B.hlw B.h4 Rp B.htm B.hNM B.hpad hinv
  obtain ⟨u1, m1, m2⟩ := Ld.nt
  have e1 := Option.some.inj (n1.symm.trans m1)
  simp only [Prod.mk.injEq] at e1
  obtain ⟨rfl, rfl, rfl⟩ := e1
  have e2 := Option.some.inj (n2.symm.trans m2)
  simp only [Prod.mk.injEq, true_and] at e2
  obtain ⟨rfl, rfl⟩ := e2
  obtain ⟨_, _, _, _, _, _, _, q6⟩ := Desc.First.K4.hearNorms_public m1
  obtain ⟨kfo, _⟩ := Desc.First.K4.hearTerms_keeps m2
  exact ⟨X, ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a13, a15, a16, a20, a23, a24, a25, a26,
    hom, hst, hsh, by rw [kfo, q6]⟩, a14, a19⟩

variable [scl : Scl] {Mm X T Wt Cl : Type} {Fr : Frame} {QF : Plan4LF Cb.Gl.E Mm X} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- **The first group's named sentence at a hearing, at the value, of the row that `pendingRowO`
returns.** -/
theorem Plan4LF.wo_ledF (A : QF.planF.MeetsF par hS pcl) (tk : Array Nat) {fo : Forest.Heard}
    {o : Own} {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
    {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}
    (h : hear engFl { par.P with tokv := tk } par.hp par.g fo F t0 = some (o, G, u))
    (Ld : LedG { par.P with tokv := tk } par.hp par.g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2
      G3 G3' G4 G5 u5)
    (nz : NzT QF.planF.fullF.ownF.toOwn.tail (ksOf { par.P with tokv := tk } par.hp)
      (t0.drop (k0 par.g)))
    (x : QF.planF.fullF.ofp.fs.X3) (g7 : Tg7)
    (I : TgRecF g7 { par.P with tokv := tk } par.hp par.g o t0 H1 tT F4 G2 G3 G3')
    (hc4 : (tailT (Plan4LF.wKF A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop (k0 par.g)) nz
        (addsOf (Plan4LF.wKF A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop (k0 par.g)) nz x
          g7)).d4.Claim
      ((tailT (Plan4LF.wKF A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop (k0 par.g)) nz
        (addsOf (Plan4LF.wKF A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop (k0 par.g)) nz x
          g7)).y4 x))
    (hx : ∀ j : Fin QF.planF.fullF.D.lT,
      QF.planF.fullF.ofp.fs.pvF x j = gl.val ((drawnOf t0).getD j.val zeroE))
    (hz0 : QF.planF.fullF.zOf (QF.planF.fullF.ofp.fs.x0F x) = zAt fo)
    (Xp : Rows.Pub34 Cb.Gl.E)
    (PX : PubAt Xp { par.P with tokv := tk } par.hp fo o G2
      ((ksOf { par.P with tokv := tk } par.hp).tc4 (t0.drop (k0 par.g))) QF.planF.fullF.D
      QF.planF.fullF.tb hS)
    (Xrd : Xp.rd = par.P.rd) (Xlk : Xp.lk = QF.planF.fullF.kW)
    (hvy : o.v.y = par.P.y) (hscl : scl = sclOf hS o.v.sc o.v.g o.v.y.Lam)
    (hL0 : o.v.g * o.v.y.Lam = QF.planF.fullF.ip.L0)
    (hn4 : ∀ q, num4 QF.planF.fullF.D QF.planF.fullF.num q =
      num4 QF.planF.fullF.D (numK QF.planF.fullF.D) q) (mm : Mm)
    (HE : ∀ cE : WsClaim,
      (envOf { par.P with tokv := tk } o).claimE o.H.ZE o.H.tkh par.P.V tk = some cE →
      tval (tenEF QF.planF.fullF
          (aS7 (Plan4LF.wKF A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop (k0 par.g)) nz x
            g7).1.1)
          (Inst.Model.Layout.Tensor.matOf (starW gl QF.planF.fullF.kW o.wo.rm
            (QF.planF.fullF.Wn (QF.planF.fullF.msg mm)))) =
        claimVal gl par.P.wsLay (starW gl QF.planF.fullF.kW o.wo.rm
          (QF.planF.fullF.Wn (QF.planF.fullF.msg mm))) cE)
    (claims : ℕ) (S : Params.LinShape) {im : ℕ} {os os' : Array Oracle} {r : TensorRow}
    (hr : pendingRowO par.P.wsLay im o.wo claims S os = .ok (r, os')) (idx : ℕ → Cb.Gl.E)
    (hidx : ∀ y ∈ r.masks, idx y.1.index = QF.planF.fullF.msg mm QF.planF.fullF.c7) :
    WoSaysF QF.planF.fullF
        (aS7 (Plan4LF.wKF A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop (k0 par.g)) nz x
          g7).1.1
        (aS7 (Plan4LF.wKF A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop (k0 par.g)) nz x
          g7).2 o.wo mm ↔
      ∑ j ∈ range (2 ^ S.kRow),
          pendWeight gl r.g j * rowAt gl par.P.wsLay.lk r.psi.reverse.toArray
            (QF.planF.fullF.Wn (QF.planF.fullF.msg mm)) j +
        (r.masks.map fun y => idx y.1.index * gl.val y.2).sum = gl.val r.target := by
  have OT := outTies_KF A tk Ld.c4
  have Sz := sevenSizesF_K A tk
  have Nm := numTiesF_K QF.planF.fullF (tailIsF_at QF.planF.fullF
    (OnBytes.Model.Verify.layerNumbers par.P par.hp par.g) A.dimIs A.wk A.hg) A.written.2.2.2.2
    (A.lamM tk)
  have hzp : ∀ j, j < QF.planF.fullF.D.lT →
      zpos QF.planF.fullF.D (zAt fo) j = gl.val (H1.ztF.getD j zeroE) := by
    intro j hj
    have q := zpos_pub Xp (by rw [PX.D, PX.v, hvy]; exact OT.lt) j (by rw [PX.D]; exact hj)
    rw [PX.D, PX.H, PX.fo, Ld.ztF] at q
    exact q
  obtain ⟨_, _, O3, O4, _, _, _⟩ := outs_of_ledF QF.planF.fullF (Plan4LF.wKF A) Ld OT nz x
    g7 I hx hz0 hzp
  have hsX : scl = sclOf Xp.h Xp.p.v.sc Xp.p.v.g Xp.p.v.y.Lam := by rw [PX.h, PX.v]; exact hscl
  have eT : Xp.tT = { tT with p := { tT.p with rowMade := true } } :=
    Option.some.inj (PX.tT.symm.trans Ld.kTT)
  have Xc : Xp.c =
      { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := tT.r } := by
    have q := PX.c
    rw [eT] at q
    exact q
  have hW : QF.planF.fullF.nW = par.hp.NCL - (if (par.g == 0) = true then 1 else 0) :=
    OnBytes.Tie.Pv.Lay.At.nW_eq QF.planF.fullF.toFullPar _ A.dimIs
  rw [if_pos A.hg] at hW
  obtain ⟨cE, _, hsz, _⟩ := ledG_merge_pub34 Ld h A.hg Xp Xc Xrd
  have h1 : Xp.cl.length + 1 = par.hp.NCL := by
    rw [← hsz, List.size_toArray, List.length_append, List.length_singleton]
  exact woSaysF_at_ledG QF.planF.fullF (Plan4LF.wKF A) Ld h A.hg nz x g7
    (addsOf (Plan4LF.wKF A) (ksOf { par.P with tokv := tk } par.hp) (t0.drop (k0 par.g)) nz x g7)
    rfl hc4 O3 O4 Sz.k3 Sz.k4 Nm.n3 Sz.hNN Sz.hLM Sz.hNE Sz.hEnd Xp PX.ρ PX.H Xc Xrd
    (by have q := PX.sh; rw [eT] at q; exact q) PX.om PX.D PX.tb
    (by rw [PX.c]; exact hL0) Xlk hsX (by rw [PX.fo]; exact hz0) (by rw [PX.fo]; exact hz0) zeroW
    (fun _ _ _ => 0) (readsTrue_zero Xp) (numK_of_num4 QF.planF.fullF.D QF.planF.fullF.num hn4)
    (by omega) mm HE claims S hr idx hidx

/-- **The first group's named sentence at a yes, of the row that `pendingRowO` returns.** -/
theorem Plan4LF.wo_atF (A : QF.planF.MeetsF par hS pcl) (L : Seat T) (Ex : ExtSpec)
    {pc : Piece (ckP .two) Fr T Cl Wt} (hds : pc.ds = dsFirst par)
    (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm) (a : T × Fr.E.Str)
    (τ : Tr (uLT (ckP .two) pc.ds)) {fo : Forest.Heard} {o : Own} {G : Fork}
    (Y : Yes L par pc a τ fo o G) (w : Wt) (hF : PscRun.Sized (L.fork a.1)) {s : WsShape}
    {lk : ℕ} {s0 : OnBytes.Model.Forest.Shape} {tl : HTailF2}
    (B : PubLines { par.P with tokv := L.tokv a.1 } par.g hS pcl QF.planF.fullF.D
      QF.planF.fullF.tb s lk s0 tl)
    (K : LookLines { par.P with tokv := L.tokv a.1 } fo s0)
    (Rp : ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
      RopeFits Reading.gl
        { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt }
        QF.planF.fullF.D QF.planF.fullF.tb (par.g * par.P.y.Lam) lam)
    (lw : ℕ → LW Cb.Gl.E) (hz0 : QF.planF.fullF.zOf (fa a).1 = zAt fo)
    (hk0 : QF.planF.fullF.kTg (fa a).1 = kTgAt fo (L.fork a.1))
    (hfil : Fo.FilledA (L.fork a.1) fo.cEnd)
    (V : Plan4L.ValueIs QF.toPlan4L par hS) (V2 : Plan4LF.ValueMoreF QF)
    (g7 : Tg7) {H1 : Heard} {hd2 : Level} {tT : Tsc}
    {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}
    (Ld : LedG { par.P with tokv := L.tokv a.1 } par.hp par.g fo o (L.fork a.1) G
      (tapeAt par pc τ) [] H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (I : TgRecF g7 { par.P with tokv := L.tokv a.1 } par.hp par.g o (tapeAt par pc τ) H1 tT F4 G2
      G3 G3')
    (HE : ∀ cE : WsClaim,
      (envOf { par.P with tokv := L.tokv a.1 } o).claimE o.H.ZE o.H.tkh par.P.V (L.tokv a.1) =
        some cE →
      tval (tenEF QF.planF.fullF
          (aS7 (Plan4F.tailMKF A (numsKF QF.planF.fullF))
            (ksOf { par.P with tokv := L.tokv a.1 } par.hp) (tb3 (tapeAt par pc τ))
            (Plan4F.nzAtF A (L.tokv a.1) hds τ _) (x3Of QF.planF (fa a).1 (tapeAt par pc τ))
            g7).1.1)
          (Inst.Model.Layout.Tensor.matOf (starW gl QF.planF.fullF.kW o.wo.rm
            (QF.planF.fullF.Wn (QF.planF.fullF.msg (part w))))) =
        claimVal gl par.P.wsLay (starW gl QF.planF.fullF.kW o.wo.rm
          (QF.planF.fullF.Wn (QF.planF.fullF.msg (part w)))) cE)
    (claims : ℕ) (S : Params.LinShape) {im : ℕ} {os os' : Array Oracle} {r : TensorRow}
    (hr : pendingRowO par.P.wsLay im o.wo claims S os = .ok (r, os')) (idx : ℕ → Cb.Gl.E)
    (hidx : ∀ y ∈ r.masks, idx y.1.index = QF.planF.fullF.msg (part w) QF.planF.fullF.c7) :
    WoSaysF QF.planF.fullF
        (aS7 (Plan4F.tailMKF A (numsKF QF.planF.fullF))
          (ksOf { par.P with tokv := L.tokv a.1 } par.hp) (tb3 (tapeAt par pc τ))
          (Plan4F.nzAtF A (L.tokv a.1) hds τ _) (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) g7).1.1
        (aS7 (Plan4F.tailMKF A (numsKF QF.planF.fullF))
          (ksOf { par.P with tokv := L.tokv a.1 } par.hp) (tb3 (tapeAt par pc τ))
          (Plan4F.nzAtF A (L.tokv a.1) hds τ _) (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) g7).2
        o.wo (part w) ↔
      ∑ j ∈ range (2 ^ S.kRow),
          pendWeight gl r.g j * rowAt gl par.P.wsLay.lk r.psi.reverse.toArray
            (QF.planF.fullF.Wn (QF.planF.fullF.msg (part w))) j +
        (r.masks.map fun y => idx y.1.index * gl.val y.2).sum = gl.val r.target := by
  obtain ⟨hinv, hscl, hvy, hL0, _, _⟩ :=
    Plan4LF.heard_KF A Y.hears hF (small_of_all _ _ _ Y.small) V.scl V.L0
  obtain ⟨Xp, PX, Xrd, Xlk⟩ := pubAtWo_of_ledF Y.hears Ld B K Rp hinv
  -- the tape behind three single drops is the tape on which the lower files speak
  have key : ∀ (t' : Tape), (tapeAt par pc τ).drop (k0 par.g) = t' →
      ∀ nz : NzT QF.planF.fullF.ownF.toOwn.tail
        (ksOf { par.P with tokv := L.tokv a.1 } par.hp) t',
      (∀ cE : WsClaim,
        (envOf { par.P with tokv := L.tokv a.1 } o).claimE o.H.ZE o.H.tkh par.P.V (L.tokv a.1) =
          some cE →
        tval (tenEF QF.planF.fullF
            (aS7 (Plan4F.tailMKF A (numsKF QF.planF.fullF))
              (ksOf { par.P with tokv := L.tokv a.1 } par.hp) t' nz
              (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) g7).1.1)
            (Inst.Model.Layout.Tensor.matOf (starW gl QF.planF.fullF.kW o.wo.rm
              (QF.planF.fullF.Wn (QF.planF.fullF.msg (part w))))) =
          claimVal gl par.P.wsLay (starW gl QF.planF.fullF.kW o.wo.rm
            (QF.planF.fullF.Wn (QF.planF.fullF.msg (part w)))) cE) →
      (WoSaysF QF.planF.fullF
          (aS7 (Plan4F.tailMKF A (numsKF QF.planF.fullF))
            (ksOf { par.P with tokv := L.tokv a.1 } par.hp) t' nz
            (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) g7).1.1
          (aS7 (Plan4F.tailMKF A (numsKF QF.planF.fullF))
            (ksOf { par.P with tokv := L.tokv a.1 } par.hp) t' nz
            (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) g7).2
          o.wo (part w) ↔
        ∑ j ∈ range (2 ^ S.kRow),
            pendWeight gl r.g j * rowAt gl par.P.wsLay.lk r.psi.reverse.toArray
              (QF.planF.fullF.Wn (QF.planF.fullF.msg (part w))) j +
          (r.masks.map fun y => idx y.1.index * gl.val y.2).sum = gl.val r.target) := by
    intro t' e
    subst e
    intro nz hE
    have hc := claims_of_ledF (Plan4F.tailMKF A (numsKF QF.planF.fullF)) Ld nz
      (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) g7 hF A.dimIs A.hg (A.lamM (L.tokv a.1)) gl_half
      (nums4_num4K QF.planF.fullF.toFullPar) I
      (first4_fullF QF.planF.fullF (Plan4F.tailMKF A (numsKF QF.planF.fullF)) Y.hears Ld A.hy B.S
        B.hs B.hg B.hrd B.hmats B.hρ A.Z B.hc B.hN B.hfl K.hsx K.hsy K.hzk K.he B.hs0 K.hpt B.Zw
        B.hsL B.hlw B.h4 Rp B.htm B.hNM B.hpad hinv hscl A.dimIs.lt hvy lw nz _ g7 I.t3 I.t4 hz0
        hk0 hfil)
    exact Plan4LF.wo_ledF A (L.tokv a.1) Y.hears Ld nz
      (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) g7 I hc.c4 (fun _ => rfl) hz0 Xp PX Xrd
      (Xlk.trans ((unitOK_of_layout B.hlw).1.symm.trans A.wk.symm)) hvy hscl hL0 V2.n4 (part w)
      hE claims S hr idx hidx
  exact key _ (tb3_eq _ A.hg) _ HE

/-- **The same with (HE) concluded, at the library's reference parameters**: `he_of_hear`
(WoEmbAt.lean) laid in. -/
theorem Plan4LF.wo_atF_ref (A : QF.planF.MeetsF par hS pcl) (L : Seat T) (Ex : ExtSpec)
    {pc : Piece (ckP .two) Fr T Cl Wt} (hds : pc.ds = dsFirst par)
    (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm) (a : T × Fr.E.Str)
    (τ : Tr (uLT (ckP .two) pc.ds)) {fo : Forest.Heard} {o : Own} {G : Fork}
    (Y : Yes L par pc a τ fo o G) (w : Wt) (hF : PscRun.Sized (L.fork a.1)) {s : WsShape}
    {lk : ℕ} {s0 : OnBytes.Model.Forest.Shape} {tl : HTailF2}
    (B : PubLines { par.P with tokv := L.tokv a.1 } par.g hS pcl QF.planF.fullF.D
      QF.planF.fullF.tb s lk s0 tl)
    (K : LookLines { par.P with tokv := L.tokv a.1 } fo s0)
    (Rp : ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
      RopeFits Reading.gl
        { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt }
        QF.planF.fullF.D QF.planF.fullF.tb (par.g * par.P.y.Lam) lam)
    (lw : ℕ → LW Cb.Gl.E) (hz0 : QF.planF.fullF.zOf (fa a).1 = zAt fo)
    (hk0 : QF.planF.fullF.kTg (fa a).1 = kTgAt fo (L.fork a.1))
    (hfil : Fo.FilledA (L.fork a.1) fo.cEnd)
    (V : Plan4L.ValueIs QF.toPlan4L par hS) (V2 : Plan4LF.ValueMoreF QF)
    (g7 : Tg7) {H1 : Heard} {hd2 : Level} {tT : Tsc}
    {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}
    (Ld : LedG { par.P with tokv := L.tokv a.1 } par.hp par.g fo o (L.fork a.1) G
      (tapeAt par pc τ) [] H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (I : TgRecF g7 { par.P with tokv := L.tokv a.1 } par.hp par.g o (tapeAt par pc τ) H1 tT F4 G2
      G3 G3')
    (hP : QF.planF.fullF.D.P = ppref) (hkR : QF.planF.fullF.kW = kRef) (hV : par.P.V = ppref.V)
    (htok : ∀ p, p < 2 ^ QF.planF.fullF.D.lT →
      QF.planF.fullF.tok (fa a).1 p = (L.tokv a.1).getD p 0)
    (N : EmbNums par.P.y)
    (claims : ℕ) (S : Params.LinShape) {im : ℕ} {os os' : Array Oracle} {r : TensorRow}
    (hr : pendingRowO par.P.wsLay im o.wo claims S os = .ok (r, os')) (idx : ℕ → Cb.Gl.E)
    (hidx : ∀ y ∈ r.masks, idx y.1.index = QF.planF.fullF.msg (part w) QF.planF.fullF.c7) :
    WoSaysF QF.planF.fullF
        (aS7 (Plan4F.tailMKF A (numsKF QF.planF.fullF))
          (ksOf { par.P with tokv := L.tokv a.1 } par.hp) (tb3 (tapeAt par pc τ))
          (Plan4F.nzAtF A (L.tokv a.1) hds τ _) (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) g7).1.1
        (aS7 (Plan4F.tailMKF A (numsKF QF.planF.fullF))
          (ksOf { par.P with tokv := L.tokv a.1 } par.hp) (tb3 (tapeAt par pc τ))
          (Plan4F.nzAtF A (L.tokv a.1) hds τ _) (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) g7).2
        o.wo (part w) ↔
      ∑ j ∈ range (2 ^ S.kRow),
          pendWeight gl r.g j * rowAt gl par.P.wsLay.lk r.psi.reverse.toArray
            (QF.planF.fullF.Wn (QF.planF.fullF.msg (part w))) j +
        (r.masks.map fun y => idx y.1.index * gl.val y.2).sum = gl.val r.target := by
  have hlk : lk = QF.planF.fullF.kW := (unitOK_of_layout B.hlw).1.symm.trans A.wk.symm
  have hl : OnBytes.Model.wsLayOf s true QF.planF.fullF.kW = .ok par.P.wsLay := by
    rw [← hlk]
    exact B.hlw
  exact Plan4LF.wo_atF A L Ex hds fa part a τ Y w hF B K Rp lw hz0 hk0 hfil V V2 g7 Ld I
    (fun cE hE => he_of_hear QF.planF.fullF (Plan4F.tailMKF A (numsKF QF.planF.fullF)) Y.hears A.hg
      (ksOf { par.P with tokv := L.tokv a.1 } par.hp) (tb3 (tapeAt par pc τ))
      (Plan4F.nzAtF A (L.tokv a.1) hds τ _) (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) g7 hP hkR hV
      A.hls.symm A.hB.symm A.dimIs.lt.symm rfl rfl htok B.Zw hl N cE hE _)
    claims S hr idx hidx

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.pubAtWo_of_ledF
#print axioms OnBytes.Road.K4.Plan4LF.wo_ledF
#print axioms OnBytes.Road.K4.Plan4LF.wo_atF
#print axioms OnBytes.Road.K4.Plan4LF.wo_atF_ref
