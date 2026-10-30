-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/IncsOutFirst.lean: THE FIRST GROUP's TWIN OF Johnson/Road/K4/IncsOut.lean: THE TYPED
FACTOR IN THE STATES OF THE LAST THREE SUMCHECKS IS THE READING OF THE CHALLENGE THAT K4's TAPE
HOLDS, from `OutIs` (OnBytes/Tie/Pv/Lay/HearTieL.lean) at the batched sumcheck's data; so
the premise hbe of `hincH5F`, `hincH6F`, `hincH7F` (Johnson/Road/K4/IncsHeardFirst.lean) is paid
from it. Statements and short proofs: IncsOut.lean's, turned to the first sub-proof's letters by a
program (as IncsHeardFirst.lean's head says); the seventh's statement by hand.

  `be4_heardF`: under `OutIs` at `aD4`: the value's `be4` of the statement behind the batched
    sumcheck is the reading of that challenge (`stack_beta`, IncsOut.lean, is taken as it stands).
  `hincO5F`, `hincO6F`, `hincO7F`: `hincH5F`, `hincH6F`, `hincH7F` with `OutIs` at `aD4` in the
    place of hbe.

Limits. `OutIs` at `aD4` is a premise; so are the ties of m to the mask (hm, hmE), `LedG`, `DimIs`,
P.y.LamM = D.ne. Equations alone: nothing on soundness or on what a mask hides.
-/
import Johnson.Road.K4.IncsOut
import Johnson.Road.K4.IncsHeardFirst

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

variable [scl : Scl] {M X0 : Type} {V : FullFPar GE M X0}
  {R : TailR} (W : TailM V.ownF.toOwn.tail R) {P : Pub} {hp : HPlan2} {g : ℕ} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}
  {fo : Forest.Heard} (L : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
  (nz : NzT V.ownF.toOwn.tail (ksOf P hp) (t0.drop (k0 g))) (x : V.ofp.fs.X3) (g7 : Tg7)
  (Hl : Fork) (hHl : Fo.Later G Hl) (mask : ℕ → GE) (entry : ℕ → ℕ → ℕ → GE) (m : V.J → GE)
  {p4 : Psc} (O4 : OutIs gl (aD4 W (ksOf P hp) (t0.drop (k0 g)) nz x g7) p4)

include O4 in
/-- **The batched sumcheck's further challenge, typed and heard.** -/
theorem be4_heardF :
    V.be4 (aZ4 W (ksOf P hp) (t0.drop (k0 g)) nz x g7).2 =
      gl.val (stackY hp.lamS ((ksOf P hp).tc4 (t0.drop (k0 g)))).2.2 :=
  O4.last.trans (congrArg gl.val (stack_beta hp.lamS ((ksOf P hp).tc4 (t0.drop (k0 g)))))

include L hHl O4 in
/-- **The gated products.** -/
theorem hincO5F (hm : m (V.cI (.inl (aH1 V.D))) = mask o.K.sH1) :
    V.ownF.toOwn.tail.s5.L.T.par.inc (aS5 W (ksOf P hp) (t0.drop (k0 g)) nz x g7) m =
      maskSum Hl (Aff.slot o.K.sH1) mask - entSum (Aff.slot o.K.sH1) entry :=
  hincH5F W L nz x g7 Hl hHl mask entry m (be4_heardF W nz x g7 O4) hm

include L hHl O4 in
/-- **The routed experts' gated products.** -/
theorem hincO6F (hD : DimIs V.D (Verify.layerNumbers P hp g)) (hLam : P.y.LamM = V.D.ne)
    (hm : ∀ i : Fin V.D.ne, m (V.cI (.inl (aH2 V.D i))) = mask (o.K.sH1 + 1 + i.val)) :
    V.ownF.toOwn.tail.s6.L.T.par.inc (aS6 W (ksOf P hp) (t0.drop (k0 g)) nz x g7) m =
      maskSum Hl (Road.Rows.start2 P.y.LamM o.K.sH1
        (drawnOf ((((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1)).toArray) mask -
      entSum (Road.Rows.start2 P.y.LamM o.K.sH1
        (drawnOf ((((ksOf P hp).tc5 (t0.drop (k0 g))).drop (P.rd.muH + 3)).drop 1)).toArray)
        entry :=
  hincH6F W L nz x g7 Hl hHl mask entry m hD hLam (be4_heardF W nz x g7 O4) hm

include L hHl O4 in
/-- **The merge, with the embedding's mask entry.** -/
theorem hincO7F (hD : DimIs V.D (Verify.layerNumbers P hp g)) (hg : (g == 0) = true)
    (hm : ∀ a : Fin V.nW, m (V.wp0.wt.nm a) = mask (o.K.sV + a.val))
    (hmE : m V.mkE = mask o.sVE) :
    V.ownF.toOwn.tail.s7.L.T.par.inc (aS7 W (ksOf P hp) (t0.drop (k0 g)) nz x g7) m =
      maskSum Hl (wsForkStart (mergeSlots hp g o)
        (powers (tapeEps ((ksOf P hp).tcW (t0.drop (k0 g)))) (mergeSlots hp g o).size)) mask -
      entSum (wsForkStart (mergeSlots hp g o)
        (powers (tapeEps ((ksOf P hp).tcW (t0.drop (k0 g)))) (mergeSlots hp g o).size)) entry :=
  hincH7F W L nz x g7 Hl hHl mask entry m hD hg (fun _ => be4_heardF W nz x g7 O4) hm hmE

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.be4_heardF
#print axioms OnBytes.Road.K4.hincO5F
#print axioms OnBytes.Road.K4.hincO6F
#print axioms OnBytes.Road.K4.hincO7F
