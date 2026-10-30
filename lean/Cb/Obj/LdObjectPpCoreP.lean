-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPpCoreP.lean: assembly of the holographic IOP from its sub-protocols: the part of the
object's record on data that knows no plan of the test for linear constraints, generic in the
request: the request is a parameter `P : LdReqPack` with its four properties `P.Good`.

A definition, statements and proofs. Generic. No assumed theorem beyond the hypotheses of its
statements.
`LdReqPack` (Cb/Obj/LdObjectDataRef.lean) is what the object's data `LdObjD`
(Cb/Obj/LdObjectTerms.lean) hold of a request.

Why: `D.CoreJ`, `D.CoreJU` (Cb/Obj/LdObjectPpCore.lean) name the reference request (its pack:
`ldRefPack`) in two clauses (reqIs, req). For `D.HypRest 1` and `Y.Hyp` the proof of `ldObjPpCore`
takes of the request's record one thing: (`ldRefPack` ..).Good (Cb/Obj/LdObjectDataRef.lean: the
request's program is in order, honest-verifier zero knowledge with its masks (`rZk : P.r.ZkS`),
formats, the end). Here that is the clause, so that every request that gives it is an instance.




Main names:
  `D.CoreP` .. (its fields: see the record).
  `Spec.ldObjPpCoreP`: E of characteristic p (`CharP E p`), `D.CoreP` .. ⇒ `D.HypRest 1` ∧ `Y.Hyp`.
  `Spec.ldObjPpCoreP_ofJ`: E of characteristic p, `D.CoreJ` .. ⇒ `D.CoreP` .. at P := the
    reference request's pack (`ldRefPack` ..): `D.CoreJ` is an instance of this record.

Notation: the `1` in `D.HypRest 1`: the argument `L` of `LdObjD.HypRest`: a natural number
(`LdCf.OK L`, Cb/Obj/LdObjectConf.lean, says that it bounds the lists at the radius of decoding).

Limits: `P.Good` is a bundle of properties of a term: this record is a door, not a record on data:
a request has to give `P.Good` from its own record (the reference request: `LdReqRefDJ`, by
`Cb.ldReqRefJ`, `Cb.ldReqStdAny`, `Cb.ldObjRef_good`, under these theorems' hypotheses).

No clause "the two languages agree".






Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectPpCore

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

/-- The clauses that know no plan, the request a parameter. -/
structure LdObjD.CoreP {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (D : LdObjD F E) (Zw : LdWfE F E) [∀ b, Fintype (Zw.K.wfI Zw.Rl b → E)] (Y : D.StdS)
    (δ : D.Dst Zw) (p : ℕ) (P : LdReqPack F E) {Fp : Type} [Field Fp] [Fintype Fp]
    [Algebra Fp E] (V : Zw.StdW Fp) : Prop where
  /-- which terms stand in D -/
  wfIs   : (⟨D.W, D.Bw⟩ : Σ W : LdOWf F E, W.P.Blk) = ⟨Zw.W, Zw.G.B⟩
  sndIs  : D = D.std Y
  reqIs  : D.pack = P
  /-- weights-formedness, the seven sendings, the index's folds -/
  wfJ    : V.HypJ p δ.dS
  sOff   : Y.TS.NearS Y.LW Y.LU Y.LO Y.tW Y.tU Y.tO δ.dW δ.dU δ.dO
  sLink  : D.K.P.StdNear Y.SdK Y.LK Y.tK Y.YK Y.ixK δ.dN
  sOn    : Y.TB.NearS Y.LWB Y.LUB Y.LOB Y.tWB Y.tUB Y.tOB δ.dWB δ.dUB δ.dOB
  own₀   : D.Own3₀
  /-- the request -/
  req    : P.Good

namespace Spec

def ldObjPpCoreP : Prop :=
  ∀ (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
      [Fintype Fp] [Algebra Fp E] (p : ℕ) [CharP E p] (D : LdObjD F E) (Zw : LdWfE F E)
      [∀ b, Fintype (Zw.K.wfI Zw.Rl b → E)] (Y : D.StdS) (δ : D.Dst Zw)
      (P : LdReqPack F E) (V : Zw.StdW Fp),
    D.CoreP Zw Y δ p P V → D.HypRest 1 ∧ Y.Hyp

def ldObjPpCoreP_ofJ : Prop :=
  ∀ (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
      [Fintype Fp] [Algebra Fp E] (Kc : Type) (p : ℕ) [CharP E p] (D : LdObjD F E) (Zw : LdWfE F E)
      [∀ b, Fintype (Zw.K.wfI Zw.Rl b → E)] (Y : D.StdS) (δ : D.Dst Zw) (R : LdORE F E Kc)
      (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞) (V : Zw.StdW Fp),
    D.CoreJ Zw Y δ p R core first b Ls T qφ q κ V →
    D.CoreP Zw Y δ p
      (ldRefPack R core first first.tgt (.nil first.tgt) (LdProg.all_nilK _ _) b Ls T qφ q) V

end Spec

theorem ldObjPpCoreP : Spec.ldObjPpCoreP := by
  intro F E Fp _ _ _ _ _ _ _ _ p _ D Zw _ Y δ P V h
  have hC : D.W.Cf.Third := by
    have key : ∀ x : Σ W : LdOWf F E, W.P.Blk, x = ⟨Zw.W, Zw.G.B⟩ → x.1.Cf.Third := by
      rintro _ rfl
      exact h.wfJ.conf3
    exact key ⟨D.W, D.Bw⟩ h.wfIs
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ :=
    ldObjZ_wf p Zw 1 (ldWfE_okStd F E Fp Zw V p 1 (ldObjRefJ_wf F E Fp Zw V p δ.dS h.wfJ))
      ⟨D.W, D.Bw⟩ h.wfIs
  have own := ldObjRefJ_own F E D h.own₀ hC
  have g : D.pack.Good := ldObjRef_at _ _ h.reqIs h.req
  exact
    ⟨{ conf := w1, lay := own.lay, tie := w2, wfLaws := w3, wfHyp := w4, wfBud := w5, wfNeed := w6,
       q₀e := own.q₀e, fold := own.fold, pyInj := own.pyInj
       fitsK := own.fitsK, foldK := own.foldK, plInj := own.plInj, bearK := own.bearK,
         rHyp := g.rHyp, rZk := g.rZk, rFmt := g.rFmt, rEnd := g.rEnd
       fitsB := own.fitsB, foldB := own.foldB, pyInjB := own.pyInjB, monoB := own.monoB },
     ⟨ldObjRefJ_lin _ E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h.sOff,
       ldObjRefJ_link _ E _ _ _ _ _ _ _ _ _ _ _ h.sLink,
       ldObjRefJ_lin _ E _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h.sOn⟩⟩

theorem ldObjPpCoreP_ofJ :
    Spec.ldObjPpCoreP_ofJ := fun F E _ _ _ _ _ _ _ _ _ Kc p _ _ _ _ _ _ R core first b Ls T qφ q κ _ h =>
  { wfIs := h.wfIs, sndIs := h.sndIs, reqIs := h.reqIs, wfJ := h.wfJ, sOff := h.sOff,
    sLink := h.sLink, sOn := h.sOn, own₀ := h.own₀
    req := ldObjRef_good F E Kc p R core first first.tgt (.nil first.tgt)
      (LdProg.all_nilK _ _) b Ls T qφ q κ
      (ldReqStdAny F E Kc p R core first b Ls T qφ q κ
        (ldReqRefJ F E Kc p R core first b Ls T qφ q κ h.req)) }

end Cb
