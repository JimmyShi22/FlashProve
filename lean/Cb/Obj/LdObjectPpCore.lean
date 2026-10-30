-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPpCore.lean: assembly of the holographic IOP from its sub-protocols: the part of the
object's record on data that knows no plan of the test for linear constraints: weights-formedness,
the seven standard senders, the index's folds, the reference request.

Definitions, statements and proofs: an assembly of the lemmas under Cb/Obj/LdObjectDataRefJ.lean,
Cb/Obj/LdObjectDataRefJU.lean, Cb/Obj/LdObjectDataRef.lean, Cb/Obj/LdObjectData.lean. Generic. No
assumed theorem beyond the hypotheses of its statements.
`LdObjD` (Cb/Obj/LdObjectTerms.lean) has the data of the object's five terms without the
closings of the two tests for linear constraints; `D.HypRest` is what is asked of them, senders and
closings apart.

Why: the records `Z.HypRefJ`, `Z.HypRefJU` are typed on `LdObjZM`, so on the plan without a
splitting (`LdLinPl`). Nine of their clauses speak of `Z.R.toLdObjD`, `Z.Zw`, `Z.Y` and the eight
distances of `Z.dst` alone, and `LdObjD` holds no plan. Here these nine stand by themselves, so that
the object at the plan of this protocol's technical report (lean/CREDITS.md;
Cb/Obj/LdObjectPlanPaper.lean: `LdObjPp` extends
`LdObjD`) can take them as they are.

Main names:
  `D.CoreJ` .. (its fields: see the record): the clauses of the same names in `Z.HypRefJ`.
  `D.CoreJU` Q ..: the same with req : `LdReqRefDJU` Q .. (Cb/Obj/LdObjectDataRefJU.lean), which has
    the hypotheses of `LdReqRefLayD Q ..` (Cb/Ld/LdLayD.lean) on the request's masks.
  `Spec.ldObjPpCore`: E of characteristic p (`CharP E p`), `D.CoreJ` .. ⇒ `D.HypRest 1`
    (Cb/Obj/LdObjectTerms.lean: all that the object asks of its parts beside senders and closings) ∧
    `Y.Hyp` ∧ "the two languages agree" at D's configuration
    (`∀ i x w, D.W.Cf.conf.Rno i x w → ∃ w', D.W.Cf.conf.Ryes i x w'`).
  `Spec.ldObjPpCoreU`: E of characteristic p, `Q.Sound`, `D.CoreJU` Q .. ⇒ `D.CoreJ` ..
  `Z.dst`; `Spec.ldObjPpCore_ofJ`, `Spec.ldObjPpCore_ofJU`: `Z.HypRefJ` .. ⇒
    `Z.R.toLdObjD.CoreJ Z.Zw Z.Y Z.dst` ..; `Z.HypRefJU` Q .. ⇒ .. `CoreJU` ..

Notation: the `1` in `D.HypRest 1`: the argument `L` of `LdObjD.HypRest`: a natural number
(`LdCf.OK L`, Cb/Obj/LdObjectConf.lean, says that it bounds the lists at the radius of decoding);
`R` (the argument, not the field `Z.R`): the end of a request and the test that follows: the data
(`LdORE`, Cb/Obj/LdObjectReqEnd.lean); `first`: the first sending: the data (`LdSendD`,
Cb/Req1/LdSegKit.lean); `Ls`: a list of reference segments, up to the stage `b` (`LdRefL`,
Cb/Req1/LdReqRef.lean); `T`: the last segment: the data (`LdRefT`, the same file); `V`: the standard
sender of weights-formedness: the data beside `Zw` (`LdWfE.StdW`, Cb/Obj/LdObjectDataSnd.lean);
`Fp`: a finite field, with `Algebra Fp E`.

Limits: this file says nothing on a plan, a closing, a whole test but the request's own. A bound to
that, at least: `Z.dst`, `Spec.ldObjPpCore_ofJ` and `Spec.ldObjPpCore_ofJU` are typed on `LdObjZM`
(see "Why"); the premises of these two statements (`Z.HypRefJ`, Cb/Obj/LdObjectDataRefJ.lean;
`Z.HypRefJU`, ..RefJU.lean) take a plan `p₀ : LdLinPl` and have fields on it (onIs, places), on the
two plans of `Z.R` (pl₁), on the link's test (pK) and on six whole tests (p₁ .. p₃, p₁B .. p₃B);
`D.CoreJ`'s and `D.CoreJU`'s field `own₀` has a clause on the link's closing (`bearK`), handed on to
the conclusion `D.HypRest 1` of `Spec.ldObjPpCore`. Agreement is still a premise: `MCArows` of
codes, in each closing of the request (`LdFoldD.IsGrpJ`, Cb/Req1/LdReqJohn.lean); in the premises
`Z.HypRefJ`, `Z.HypRefJU` also in the three towers of the test at N instances (p₁B .. p₃B:
`LdRunD.PreJ`, field `tow`: `MCArows`, at a base case `MCAat`). The declared differences in the
heads of Cb/Obj/LdObjectDataRefJ.lean and Cb/Req1/LdReqJohn.lean hold here too.
No instance in this file. No theorem of this library states that the hypotheses of `ldObjPpCore` can
be met together.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectDataRefJU

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- the distances of the oracle messages sent -/
structure LdObjD.Dst (D : LdObjD F E) (Zw : LdWfE F E) where
  dS   : Zw.W.P.S.O → ℕ
  dW   : D.W.O.toC.P.NW.O → ℕ
  dU   : D.W.O.toC.P.NU.O → ℕ
  dO   : D.W.O.toC.P.NO.O → ℕ
  dN   : D.K.P.N.O → ℕ
  dWB  : D.on.ol.toC.P.NW.O → ℕ
  dUB  : D.on.ol.toC.P.NU.O → ℕ
  dOB  : D.on.ol.toC.P.NO.O → ℕ

/-- The nine clauses that know no plan. -/
structure LdObjD.CoreJ (D : LdObjD F E) (Zw : LdWfE F E) [∀ b, Fintype (Zw.K.wfI Zw.Rl b → E)]
    (Y : D.StdS) (δ : D.Dst Zw) (p : ℕ) {Kc : Type} (R : LdORE F E Kc)
    (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
    (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
    (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
    (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
    (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) {Fp : Type} [Field Fp] [Fintype Fp]
    [Algebra Fp E] (V : Zw.StdW Fp) : Prop where
  /-- which terms stand in D -/
  wfIs   : (⟨D.W, D.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨Zw.W, Zw.G.B⟩
  sndIs  : D = D.std Y
  reqIs  : D.pack =
    ldRefPack R core first first.tgt (.nil first.tgt) (LdProg.all_nilK _ _) b Ls T qφ q
  /-- weights-formedness, the seven sendings, the index's folds -/
  wfJ    : V.HypJ p δ.dS
  sOff   : Y.TS.NearS Y.LW Y.LU Y.LO Y.tW Y.tU Y.tO δ.dW δ.dU δ.dO
  sLink  : D.K.P.StdNear Y.SdK Y.LK Y.tK Y.YK Y.ixK δ.dN
  sOn    : Y.TB.NearS Y.LWB Y.LUB Y.LOB Y.tWB Y.tUB Y.tOB δ.dWB δ.dUB δ.dOB
  own₀   : D.Own3₀
  /-- the request -/
  req    : LdReqRefDJ p R core first b Ls T qφ q κ

/-- The same, with the hypotheses of `LdReqRefLayD Q ..` (Cb/Ld/LdLayD.lean) on the request's
masks. -/
structure LdObjD.CoreJU (D : LdObjD F E) (Zw : LdWfE F E) [∀ b, Fintype (Zw.K.wfI Zw.Rl b → E)]
    (Y : D.StdS) (δ : D.Dst Zw) (Q : LdLayQ E) (p : ℕ) {Kc : Type} (R : LdORE F E Kc)
    (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
    (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
    (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
    (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
    (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) {Fp : Type} [Field Fp] [Fintype Fp]
    [Algebra Fp E] (V : Zw.StdW Fp) : Prop where
  wfIs   : (⟨D.W, D.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨Zw.W, Zw.G.B⟩
  sndIs  : D = D.std Y
  reqIs  : D.pack =
    ldRefPack R core first first.tgt (.nil first.tgt) (LdProg.all_nilK _ _) b Ls T qφ q
  wfJ    : V.HypJ p δ.dS
  sOff   : Y.TS.NearS Y.LW Y.LU Y.LO Y.tW Y.tU Y.tO δ.dW δ.dU δ.dO
  sLink  : D.K.P.StdNear Y.SdK Y.LK Y.tK Y.YK Y.ixK δ.dN
  sOn    : Y.TB.NearS Y.LWB Y.LUB Y.LOB Y.tWB Y.tUB Y.tOB δ.dWB δ.dUB δ.dOB
  own₀   : D.Own3₀
  req    : LdReqRefDJU Q p R core first b Ls T qφ q κ

/-- the distances of an object at the plan without a splitting -/
def LdObjZM.dst (Z : LdObjZM F E) : Z.R.toLdObjD.Dst Z.Zw :=
  ⟨Z.dS, Z.dW, Z.dU, Z.dO, Z.dN, Z.dWB, Z.dUB, Z.dOB⟩

end

namespace Spec

def ldObjPpCore_ofJ : Prop :=
  ∀ (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
      [Fintype Fp] [Algebra Fp E] (Kc : Type) (p : ℕ) (Z : LdObjZM F E)
      [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (R : LdORE F E Kc)
      (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) (V : Z.Zw.StdW Fp)
      (p₀ : LdLinPl R.O.d.ol.toC) (plR : R.Bn → R.S.Ent → Prop),
    Z.HypRefJ p R core first b Ls T qφ q κ V p₀ plR →
    Z.R.toLdObjD.CoreJ Z.Zw Z.Y Z.dst p R core first b Ls T qφ q κ V

def ldObjPpCore_ofJU : Prop :=
  ∀ (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
      [Fintype Fp] [Algebra Fp E] (Kc : Type) (p : ℕ) (Z : LdObjZM F E)
      [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (R : LdORE F E Kc)
      (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) (V : Z.Zw.StdW Fp) (p₀ : LdLinPl R.O.d.ol.toC)
      (plR : R.Bn → R.S.Ent → Prop) (Q : LdLayQ E),
    Z.HypRefJU Q p R core first b Ls T qφ q κ V p₀ plR →
    Z.R.toLdObjD.CoreJU Z.Zw Z.Y Z.dst Q p R core first b Ls T qφ q κ V

def ldObjPpCore : Prop :=
  ∀ (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
      [Fintype Fp] [Algebra Fp E] (Kc : Type) (p : ℕ) [CharP E p] (D : LdObjD F E) (Zw : LdWfE F E)
      [∀ b, Fintype (Zw.K.wfI Zw.Rl b → E)] (Y : D.StdS) (δ : D.Dst Zw) (R : LdORE F E Kc)
      (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) (V : Zw.StdW Fp),
    D.CoreJ Zw Y δ p R core first b Ls T qφ q κ V →
    D.HypRest 1 ∧ Y.Hyp ∧ ∀ i x w, D.W.Cf.conf.Rno i x w → ∃ w', D.W.Cf.conf.Ryes i x w'

def ldObjPpCoreU : Prop :=
  ∀ (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
      [Fintype Fp] [Algebra Fp E] (Kc : Type) (p : ℕ) [CharP E p] (D : LdObjD F E) (Zw : LdWfE F E)
      [∀ b, Fintype (Zw.K.wfI Zw.Rl b → E)] (Y : D.StdS) (δ : D.Dst Zw) (R : LdORE F E Kc)
      (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) (V : Zw.StdW Fp),
    ∀ Q : LdLayQ E, Q.Sound → D.CoreJU Zw Y δ Q p R core first b Ls T qφ q κ V →
      D.CoreJ Zw Y δ p R core first b Ls T qφ q κ V

end Spec

theorem ldObjPpCore_ofJ :
    Spec.ldObjPpCore_ofJ := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h =>
  ⟨h.wfIs, h.sndIs, h.reqIs, h.wfJ, h.sOff, h.sLink, h.sOn, h.own₀, h.req⟩

theorem ldObjPpCore_ofJU :
    Spec.ldObjPpCore_ofJU := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h =>
  ⟨h.wfIs, h.sndIs, h.reqIs, h.wfJ, h.sOff, h.sLink, h.sOn, h.own₀, h.req⟩

theorem ldObjPpCore : Spec.ldObjPpCore := by
  intro F E Fp _ _ _ _ _ _ _ _ Kc p _ D Zw _ Y δ R core first b Ls T qφ q κ V h
  have hC : D.W.Cf.Third := by
    have key : ∀ x : Σ W : LdOWf F E, W.P.Blk, x = ⟨Zw.W, Zw.G.B⟩ → x.1.Cf.Third := by
      rintro _ rfl
      exact h.wfJ.conf3
    exact key ⟨D.W, D.Bw⟩ h.wfIs
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ :=
    ldObjZ_wf p Zw 1 (ldWfE_okStd F E Fp Zw V p 1 (ldObjRefJ_wf F E Fp Zw V p δ.dS h.wfJ))
      ⟨D.W, D.Bw⟩ h.wfIs
  have own := ldObjRef_own F E Kc p D R core first first.tgt (.nil first.tgt) (LdProg.all_nilK _ _)
    b Ls T qφ q κ h.reqIs (ldObjRefJ_own F E D h.own₀ hC)
    (ldReqStdAny F E Kc p R core first b Ls T qφ q κ
      (ldReqRefJ F E Kc p R core first b Ls T qφ q κ h.req))
  exact
    ⟨{ conf := w1, lay := own.lay, tie := w2, wfLaws := w3, wfHyp := w4, wfBud := w5, wfNeed := w6,
       q₀e := own.q₀e, fold := own.fold, pyInj := own.pyInj
       fitsK := own.fitsK, foldK := own.foldK, plInj := own.plInj, bearK := own.bearK,
         rHyp := own.rHyp, rZk := own.rZk, rFmt := own.rFmt, rEnd := own.rEnd
       fitsB := own.fitsB, foldB := own.foldB, pyInjB := own.pyInjB, monoB := own.monoB },
     ⟨ldObjRefJ_lin _ E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h.sOff,
       ldObjRefJ_link _ E _ _ _ _ _ _ _ _ _ _ _ h.sLink,
       ldObjRefJ_lin _ E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h.sOn⟩,
     ldLangs_at D.W.Cf R.Cf (congrArg LdReqPack.Cf h.reqIs) h.req.duty.langs⟩

theorem ldObjPpCoreU :
    Spec.ldObjPpCoreU := fun F E _ _ _ _ _ _ _ _ _ Kc p _ _ _ _ _ _ R core first b Ls T qφ q κ _ Q hQ h =>
  { wfIs := h.wfIs, sndIs := h.sndIs, reqIs := h.reqIs, wfJ := h.wfJ, sOff := h.sOff,
    sLink := h.sLink, sOn := h.sOn, own₀ := h.own₀
    req := ldReqRefJU F E Kc p R core first b Ls T qφ q κ Q hQ h.req }

end Cb
