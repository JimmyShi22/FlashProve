-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappaObj.lean: "every round's error, as a probability, is at most κ" (`Err.Below`,
Iop/InteractiveOracleProof.lean): the object's five lists, level by level. The quoted words say e ≤ κ · v, with e the
round's error, a count of values of its verifier message (`Err`, Iop/Rbr.lean), and v the number of
all values of that message.

Theorems: glue. Nothing is evaluated. The five lists are the errors of the protocol's sub-protocols:
weights-formedness, the test for linear constraints at one instance, the link, a request's preamble,
the test at N instances. These errors are numbers that the object lists (`obj.nums`,
Cb/Obj/LdObject.lean: a `SubsR.Nums`, Hiop/RecBuild.lean, whose five entries each have the data
field `err`): that a sub-protocol is sound at the numbers that are listed for it is no statement of
this file; that tie is `Spec.ldObj_hyp` (Cb/Obj/LdObject.lean), under `Obj.OK L`, in the sense of
`SubsR.HypK` (Hiop/RecBuild.lean) (that condition itself asks soundness of the parts one level
down: the tie carries soundness, it does not found it).

Main names:
  `ldKappa_objT`: the object with the parts' terms (`LdObjT`: both closings parameters):
    `T.obj.nums.Below κ` from: weights-formedness (`T.Bw.Kap κ`); the core of the test for linear
    constraints at one instance and its closing's chain; the link's core and its one test; the
    request (`T.r.Below κ`: Cb/Req1/LdReqBelow.lean); the core at N instances and its closing's
    chain for a batch.
  `ldKappa_objP`: both closings at the plan (`LdObjP`): the two tests of each plan, and "the rest"
    of each as a chain. (not all hypotheses are named here: see its statement)
  `ldKappa_objR`: "the rest" of each plan one more test (`LdObjR`): seven tests. (not all hypotheses
    are named here: see its statement)

Notation: `Bw.Kap` (Cb/Ld/LdKappaBat.lean): weights-formedness: its numbers, and its blocks' lists;
`KapC` (Cb/Ld/LdKappaKit.lean): the core of the test for linear constraints, of the link: its
numbers; `KapCB` (Cb/Ld/LdKappaBat.lean): the core at N instances: its numbers; `run.Kap`
(Cb/Ld/LdKappaRun.lean): one whole test on a group: its numbers, and its test's list (`test`); of a
chain, `ErrBelow` (Cb/Req1/LdReqBelow.lean): every link's list of errors, as a probability, is at
most κ, round by round; `ErrBelowA` (Cb/Ld/LdKappaBat.lean): the like of every link's list of errors
for a batch.

Limits: this file says nothing on the size of any number. It says nothing on the record `Z.Kap κ`
and the statement for quoting, `Spec.ldKappa`: Cb/Ld/LdKappa.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdKappaTow
import Cb.Ld.LdKappaBat
import Cb.Obj.LdObjectPlanRows

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain IOR.ChainA
open scoped ENNReal

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem errBelowA_of_eq {K : Type} {A B : Joint K} {c c' : ChainA K A B} (e : c = c')
    (κ : ℝ≥0∞) (h : c'.ErrBelowA κ) : c.ErrBelowA κ := e ▸ h

theorem ldKappa_objT (T : LdObjT F E) (κ : ℝ≥0∞) (hW : T.Bw.Kap κ)
    (hL : T.W.O.toC.P.KapC T.Sn T.εf κ) (hQ : T.Qt.c.ErrBelow κ)
    (hK : T.K.P.KapC T.Sl T.ε₀ T.ε₁ κ) (hKc : T.Kc.run.Kap κ) (hR : T.r.Below κ)
    (hB : T.on.ol.toC.P.KapCB T.SnB T.εfB T.N κ) (hZ : T.cZ.forget.ErrBelowA κ) :
    T.obj.nums.Below κ := by
  refine ⟨ldKappa_wf T.Bw κ hW, ?_, ?_, (ldReq_below E T.Kr).2 _ _ _ _ _ T.r T.w₀ κ hR, ?_⟩
  · exact (ldKappa_linC T.W.O.toC.P T.W.O.on0 T.Sn T.εf (T.W.O.toC.cZ T.Qt T.fq) T.dT κ hL
      (ldKappa_linZ T.W.O.toC T.Qt T.fq κ hQ))
  · exact (ldKappa_linkC T.K.P T.on0K T.on1K T.Sl T.ε₀ T.ε₁ (T.Kc.cZ T.dK₂)
      T.dK κ hK (ldKappa_linkZ T.K.P T.Kc T.dK₂ κ hKc))
  · show Err.Below (T.on.ol.termV T.onB T.SnB T.qaB T.εfB T.N T.cZ T.dB T.dB₀).a.err κ
    rw [(ldOnT_same F E T.on.ol T.onB T.SnB T.qaB T.εfB T.N T.VT T.cZ T.dB T.dB₀).1]
    exact (ldKappa_linCA T.on.ol.toC.P T.onB T.SnB T.εfB T.N T.cZ.forget T.dB κ hB hZ)

theorem ldKappa_objP (P : LdObjP F E) (κ : ℝ≥0∞) (hW : P.Bw.Kap κ)
    (hL : P.W.O.toC.P.KapC P.Sn P.εf κ) (h₁ : P.TP.D₁.Kap κ) (h₂ : P.TP.D₂.Kap κ)
    (hQ : P.TP.Q'.c.ErrBelow κ) (hK : P.K.P.KapC P.Sl P.ε₀ P.ε₁ κ) (hKc : P.Kc.run.Kap κ)
    (hR : P.r.Below κ) (hB : P.on.ol.toC.P.KapCB P.SnB P.εfB P.N κ) (h₁B : P.TB.D₁.Kap κ)
    (h₂B : P.TB.D₂.Kap κ) (hQB : P.cA'.ErrBelowA κ) : P.toT.obj.nums.Below κ := by
  refine ldKappa_objT P.toT κ hW hL ?_ hK hKc hR hB ?_
  · exact ldKappa_cons P.TP.D₁ _ _ _ κ h₁ (ldKappa_cons P.TP.D₂ _ _ _ κ h₂ hQ)
  · show P.cZ.forget.ErrBelowA κ
    unfold LdObjP.cZ LdLinPlT.cZV
    have e := (ldLinV_cZ_same E _ _ _ _ P.on.ol.toC P.N (P.TB.QA P.cA' P.same') P.TB.fq
      (P.on.ol.toC.P.V6 P.SnB P.qaB P.N) (P.TB.tie₀ P.tie') (P.TB.qB₀ P.N P.q₀B P.bB')
      (P.TB.QV P.N P.q₀B P.bB' P.tie' P.cA' P.same' P.x₀ P.QV')).1
    refine errBelowA_of_eq e κ (ldKappa_linZA P.on.ol.toC (P.TB.QA P.cA' P.same') P.TB.fq κ ?_)
    exact (ldKappa_consSh P.TB.D₁ _ _ _ κ h₁B
      (ldKappa_consLo P.TB.D₂ ⟨P.TB.Q', P.cA', P.same'⟩ _ _ κ h₂B hQB))

theorem ldKappa_objR (R : LdObjR F E) (κ : ℝ≥0∞) (hW : R.Bw.Kap κ)
    (hL : R.W.O.toC.P.KapC R.Sn R.εf κ) (h₁ : R.TP₀.D₁.Kap κ) (h₂ : R.TP₀.D₂.Kap κ)
    (h₃ : R.X.run.Kap κ) (hK : R.K.P.KapC R.Sl R.ε₀ R.ε₁ κ) (hKc : R.Kc.run.Kap κ)
    (hR : R.r.Below κ) (hB : R.on.ol.toC.P.KapCB R.SnB R.εfB R.N κ) (h₁B : R.TB₀.D₁.Kap κ)
    (h₂B : R.TB₀.D₂.Kap κ) (h₃B : R.XB.run.Kap κ) : R.toP.toT.obj.nums.Below κ :=
  ldKappa_objP R.toP κ hW hL h₁ h₂ (ldKappa_cons R.X.run _ _ _ κ h₃ (ldKappa_nil _ _ _ κ))
    hK hKc hR hB h₁B h₂B (ldKappa_consLo R.XB.run _ _ _ κ h₃B (ldKappa_nilA _ κ))

end
end Cb
