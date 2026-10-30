-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/GrindKRecut.lean: `Spec.soundAtK_recut`, `Spec.soundKG_recut`: each under the hypotheses
of its statement, knowledge soundness with named lists of errors, and the bound that counts proof
of work, are carried along when rounds are cut and joined at the interface.

Statements and proofs.
A plan (`XPlan s`, Iop/Recut.lean) goes through the rounds of a shape s: it keeps the first round,
cuts a first piece off it, or joins it with the second. The pass on an interface is `BatchProtocol.recut`
(Iop/BatchRecut.lean).
CompileK/KnowRecut.lean shows (`Spec.soundK_recut`, under the hypotheses of its statement) that
`BatchProtocol.SoundK` is kept by a pass of cuts and joins (`BatchProtocol.recut`), at one number. This file does it
for the form with the lists written out (`BatchProtocol.SoundAtK`, Hiop/GrindK.lean), and for `BatchProtocol.SoundKG`
(each round's error at most c once its bits of work are credited).

Main names, each under the hypotheses of its statement:
  `Spec.soundAtK_recut`: SoundAtK is kept: the lists `Err.recut` (a first piece that is cut off has
    the error 0; a joined round e1 |C2| + |C1| e2), the witness map on the same symbols
    (`Orcs.old`). Any lawful plans, joins of two verifier messages included.
  `Spec.soundKG_recut`: SoundKG is kept at the same c, with the numbers of test bits carried by
    `GBits.recut` (Iop/GrindRecut.lean: they stay with the piece, or the joined round, that has the
    verifier message), for plans that join no two verifier messages (`XPlan.NoChal`).
  `Spec.soundAtK_join`, `Spec.soundKG_join`: the same for the pass "every marked round joins the
    next prover message" (`BatchProtocol.join`, CompileK/KnowJoin.lean).

The conditions are those of CompileK/KnowRecut.lean (of them `soundAtK_recut` does not ask `XT.OK`,
`XL.OK` and the three `XPlan.NoChal`; likewise `soundAtK_join`: of the marks `μB.OK` alone;
`soundAtK_join` and `soundKG_join` ask `L.late = none`), with one change. There "a round whose
verifier message has one value has the error 0" (`Err.UnitZero`) follows from εs < 1. With work it
does not: c 2^b may be 1 or more. So `soundAtK_recut` asks it of the session's list, and
`soundKG_recut` asks c < 1 and that a round whose verifier message has one value has no test
(`GBits.UnitFree`, Ior/GrindKLists.lean).
So work may be given before the pass, by the names of the rounds as the sub-protocols have them, or
after it, on the shapes of the interface that is compiled (`Work`, CompileK/GrindMain.lean): under
the hypotheses of `Spec.soundKG_recut` the first gives the second.

Limits: this file says nothing on the honest side (`propsK_recut`, CompileK/KnowRecut.lean, under
the hypotheses of its statement, keeps all of `BatchProtocol.PropsK` with the same numbers; that theorem asks
M.εs < 1 of the bare errors). This file says nothing on any instance. At a join of two verifier
messages errors add while bits take the maximum: no bound is carried there.

Terms: lean/GLOSSARY.md.
-/
import CompileK.KnowJoin
import Hiop.GrindK
import Ior.GrindKLists

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace Spec

/-- Under the hypotheses below, knowledge soundness for explicit lists is kept by a pass of cuts
and joins. -/
def soundAtK_recut : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop) (wit : X → Orcs L.onlineBatch.loc.shape → Wn)
      (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape)
      (XT : XPlan L.offline.shape) (XL : XPlan L.link.shape) (XB : XPlan L.onlineBatch.loc.shape)
      (ZB : AXPlan XB L.onlineBatch.ann) (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB),
    XB.OK → AXPlan.OK XB L.onlineBatch.ann ZB → 0 < L.maxBatchSize →
    (∀ n, L.late = some n → AXPlan.Late XB L.onlineBatch.ann ZB n) →
    εB.UnitZero → L.SoundAtK Rno wit εT εL εB →
    (L.recut XT XL XB ZB hK).SoundAtK
      Rno (fun x o => wit x (Orcs.old XB o)) (Err.recut XT εT) (Err.recut XL εL) (Err.recut XB εB)

/-- Given the hypotheses below, a pass of cuts and joins keeps `BatchProtocol.SoundKG` (each round's error
within c, its bits of work credited) at the very same c. -/
def soundKG_recut : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop) (wit : X → Orcs L.onlineBatch.loc.shape → Wn)
      (gT : GBits L.offline.shape) (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (c : ℝ≥0∞)
      (XT : XPlan L.offline.shape) (XL : XPlan L.link.shape) (XB : XPlan L.onlineBatch.loc.shape)
      (ZB : AXPlan XB L.onlineBatch.ann) (hK : AXPlan.Kinds XB L.onlineBatch.ann ZB),
    XT.OK → XL.OK → XB.OK → XT.NoChal → XL.NoChal → XB.NoChal → AXPlan.OK XB L.onlineBatch.ann ZB →
    0 < L.maxBatchSize → (∀ n, L.late = some n → AXPlan.Late XB L.onlineBatch.ann ZB n) → c < 1 → gT.UnitFree →
    gL.UnitFree → gB.UnitFree → L.SoundKG Rno wit gT gL gB c →
    (L.recut XT XL XB ZB hK).SoundKG
      Rno (fun x o => wit x (Orcs.old XB o)) (gT.recut XT) (gL.recut XL) (gB.recut XB) c

/-- the same for the pass "every marked round joins the next prover message" -/
def soundAtK_join : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop) (wit : X → Orcs L.onlineBatch.loc.shape → Wn)
      (εT : Err L.offline.shape) (εL : Err L.link.shape) (εB : Err L.onlineBatch.loc.shape)
      (μT : Marks L.offline.shape) (μL : Marks L.link.shape) (μB : Marks L.onlineBatch.loc.shape),
    μB.OK → 0 < L.maxBatchSize → L.late = none → εB.UnitZero → L.SoundAtK Rno wit εT εL εB →
    (L.join μT μL μB).SoundAtK Rno (fun x o => wit x (Orcs.old (XPlan.ofMarks μB) o))
      (Err.recut (XPlan.ofMarks μT) εT) (Err.recut (XPlan.ofMarks μL) εL)
      (Err.recut (XPlan.ofMarks μB) εB)

def soundKG_join : Prop :=
  ∀ (I X Wn : Type) (L : BatchProtocol I X) (Rno : I → X → Wn → Prop) (wit : X → Orcs L.onlineBatch.loc.shape → Wn)
      (gT : GBits L.offline.shape) (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) (c : ℝ≥0∞)
      (μT : Marks L.offline.shape) (μL : Marks L.link.shape) (μB : Marks L.onlineBatch.loc.shape),
    μT.OK → μL.OK → μB.OK → 0 < L.maxBatchSize → L.late = none → c < 1 → gT.UnitFree → gL.UnitFree →
    gB.UnitFree → L.SoundKG Rno wit gT gL gB c →
    (L.join μT μL μB).SoundKG Rno (fun x o => wit x (Orcs.old (XPlan.ofMarks μB) o))
      (gT.recut (XPlan.ofMarks μT)) (gL.recut (XPlan.ofMarks μL)) (gB.recut (XPlan.ofMarks μB)) c

end Spec

theorem soundAtK_recut :
    Spec.soundAtK_recut := fun _ _ _ L _ wit _ _ εB XT XL XB ZB hK hB hZ hN hl hu h =>
  ⟨h.sndT.recut XT, h.sndL.recut XL,
    sndBK_recut _ _ _ L.onlineBatch XB ZB hB hZ hK L.maxBatchSize hN L.early L.late hl _ wit εB hu h.sndB⟩

theorem soundKG_recut : Spec.soundKG_recut := by
  rintro I X Wn L Rno wit gT gL gB c XT XL XB ZB hK hT hL hB nT nL nB hZ hN hl hc uT uL
    uB ⟨εT, εL, εB, hA, bT, bL, bB⟩
  have zT := unitZero_of_belowG _ gT εT c hc uT bT
  have zL := unitZero_of_belowG _ gL εL c hc uL bL
  have zB := unitZero_of_belowG _ gB εB c hc uB bB
  exact ⟨_, _, _,
    soundAtK_recut I X Wn L Rno wit εT εL εB XT XL XB ZB hK hB hZ hN hl zB hA,
    belowG_recut _ XT hT nT gT εT c zT bT,
    belowG_recut _ XL hL nL gL εL c zL bL,
    belowG_recut _ XB hB nB gB εB c zB bB⟩

theorem soundAtK_join : Spec.soundAtK_join := fun I X Wn L Rno wit εT εL εB _ _ μB hB hN hl hu h =>
  soundAtK_recut I X Wn L Rno wit εT εL εB _ _ _ _ _ (XPlan.ofMarks_ok μB hB)
    (AXPlan.noCut_ok _ _ _) hN (fun n hn => by rw [hl] at hn; cases hn) hu h

theorem soundKG_join :
    Spec.soundKG_join := fun I X Wn L Rno wit gT gL gB c μT μL μB hT hL hB hN hl hc uT uL uB h =>
  soundKG_recut I X Wn L Rno wit gT gL gB c _ _ _ _ _ (XPlan.ofMarks_ok μT hT)
    (XPlan.ofMarks_ok μL hL) (XPlan.ofMarks_ok μB hB) (XPlan.ofMarks_noChal μT)
    (XPlan.ofMarks_noChal μL) (XPlan.ofMarks_noChal μB) (AXPlan.noCut_ok _ _ _) hN
    (fun n hn => by rw [hl] at hn; cases hn) hc uT uL uB h

end Iop
