-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/IncsOut.lean: THE TYPED FACTOR IN THE STATES OF THE LAST THREE SUMCHECKS IS THE
READING OF THE CHALLENGE THAT K4's TAPE HOLDS, from `OutIs`
(OnBytes/Tie/Pv/Lay/HearTieL.lean) at the batched sumcheck's data; so the premise hbe of `hincH5`,
`hincH6`, `hincH7` (Johnson/Road/K4/IncsHeard.lean) is paid from it. Statements and short proofs.

  `stack_beta`: the further challenge that the chain's data read off the batched sumcheck's tape is
    the one that K4's reading of that tape names, `(stackY lamS t).2.2`: two cuts of one tape.
  `be4_heard`: under `OutIs` at `aD4`: the value's `be4` of the statement behind the batched
    sumcheck is the reading of that challenge.
  `hincO5`, `hincO6`, `hincO7`: `hincH5`, `hincH6`, `hincH7` with `OutIs` at `aD4` in the place of
    hbe.

Limits. `OutIs` at `aD4` is a premise; so are the ties of m to the mask (hm), `Led7`, `DimIs`,
P.y.LamM = D.ne. Equations alone: nothing on soundness or on what a mask hides. A group that is not
the first.
-/
import Johnson.Road.K4.IncsHeard
import OnBytes.Tie.Pv.Lay.HearTieL

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Desc.First OnBytes.Desc.First.K4 OnBytes.Slice
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open OnBytes.Tie.Pv.Lay (OutIs)
open OnBytes.Tie.Pv.Lay.At (DimIs)
open OnBytes.Desc.First.P1 (gl drawnOf tapeEps Ks NzT Tg7 TailM TailR pscT aS5 aS6 aS7 aD4 aZ4)

/-- Two cuts of one tape. -/
theorem stack_beta (lamS : ℕ) (t : Tape) :
    (pscT 0 lamS (t.drop 1)).beta = (stackY lamS t).2.2 := by
  have dy : (t.drop 1).drop (lamS + 1) = t.drop (lamS + 2) := by
    rw [drop_drop' 1 (lamS + 1) t]
    congr 1
    omega
  show (P1.roundAt (OnBytes.Psc.Weight.atZero 1) ((t.drop 1).drop (lamS + 1))).2.2 = _
  rw [dy]
  rfl

variable [scl : Scl] {M X0 : Type} {V : FullPar GE M X0}
  {R : TailR} (W : TailM V.own.toOwn.tail R) {P : Pub} {hp : HPlan2} {g : ℕ} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}
  {fo : Forest.Heard} (L : Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
  (nz : NzT V.own.toOwn.tail (ksOf P hp) (t0.drop 1)) (x : V.XT) (g7 : Tg7)
  (Hl : Fork) (hHl : Fo.Later G Hl) (mask : ℕ → GE) (entry : ℕ → ℕ → ℕ → GE) (m : V.J → GE)
  {p4 : Psc} (O4 : OutIs gl (aD4 W (ksOf P hp) (t0.drop 1) nz x g7) p4)

include O4 in
/-- **The batched sumcheck's further challenge, typed and heard.** -/
theorem be4_heard :
    V.be4 (aZ4 W (ksOf P hp) (t0.drop 1) nz x g7).2 =
      gl.val (stackY hp.lamS ((ksOf P hp).tc4 (t0.drop 1))).2.2 :=
  O4.last.trans (congrArg gl.val (stack_beta hp.lamS ((ksOf P hp).tc4 (t0.drop 1))))

include L hHl O4 in
/-- **The gated products.** -/
theorem hincO5 (hm : m (V.cI (.inl (aH1 V.D))) = mask o.K.sH1) :
    V.own.toOwn.tail.s5.L.T.par.inc (aS5 W (ksOf P hp) (t0.drop 1) nz x g7) m =
      maskSum Hl (Aff.slot o.K.sH1) mask - entSum (Aff.slot o.K.sH1) entry :=
  hincH5 W L nz x g7 Hl hHl mask entry m (be4_heard W nz x g7 O4) hm

include L hHl O4 in
/-- **The routed experts' gated products.** -/
theorem hincO6 (hD : DimIs V.D (Verify.layerNumbers P hp g)) (hLam : P.y.LamM = V.D.ne)
    (hm : ∀ i : Fin V.D.ne, m (V.cI (.inl (aH2 V.D i))) = mask (o.K.sH1 + 1 + i.val)) :
    V.own.toOwn.tail.s6.L.T.par.inc (aS6 W (ksOf P hp) (t0.drop 1) nz x g7) m =
      maskSum Hl (Road.Rows.start2 P.y.LamM o.K.sH1
        (drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1)).toArray) mask -
      entSum (Road.Rows.start2 P.y.LamM o.K.sH1
        (drawnOf ((((ksOf P hp).tc5 (t0.drop 1)).drop (P.rd.muH + 3)).drop 1)).toArray) entry :=
  hincH6 W L nz x g7 Hl hHl mask entry m hD hLam (be4_heard W nz x g7 O4) hm

include L hHl O4 in
/-- **The merge.** -/
theorem hincO7 (hD : DimIs V.D (Verify.layerNumbers P hp g)) (hg : (g == 0) = false)
    (hm : ∀ a : Fin V.nW, m (V.wp0.wt.nm a) = mask (o.K.sV + a.val)) :
    V.own.toOwn.tail.s7.L.T.par.inc (aS7 W (ksOf P hp) (t0.drop 1) nz x g7) m =
      maskSum Hl (wsForkStart ((Array.range (hp.NCL - 0)).map (o.K.sV + ·) ++ #[])
        (powers (tapeEps ((ksOf P hp).tcW (t0.drop 1)))
          ((Array.range (hp.NCL - 0)).map (o.K.sV + ·) ++ #[]).size)) mask -
      entSum (wsForkStart ((Array.range (hp.NCL - 0)).map (o.K.sV + ·) ++ #[])
        (powers (tapeEps ((ksOf P hp).tcW (t0.drop 1)))
          ((Array.range (hp.NCL - 0)).map (o.K.sV + ·) ++ #[]).size)) entry :=
  hincH7 W L nz x g7 Hl hHl mask entry m hD hg (fun _ => be4_heard W nz x g7 O4) hm

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.stack_beta
#print axioms OnBytes.Road.K4.be4_heard
#print axioms OnBytes.Road.K4.hincO5
#print axioms OnBytes.Road.K4.hincO6
#print axioms OnBytes.Road.K4.hincO7
