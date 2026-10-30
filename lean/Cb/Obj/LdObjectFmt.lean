-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectFmt.lean: the session of the object at the terms of Cb/Obj/LdObjectTerms.lean
(`LdObjT`) has the format that the compiled scheme can carry, under a condition on the batch test's
closing.

Book-keeping for the compiled scheme: the kind of a round and its phase fix the format of the
verifier's Fiat-Shamir query (Iop/BatchFmt.lean). This file is about the order of the kinds in a
session: in a shared round the verifier message is one for all slots, in a local round each slot
has its own (Iop/Batch.lean).

Statements (`Cb.Spec.ldOnT_runs`, `ldPlan_runs`, `ldObjT_fmt`, `ldObjP_fmt`) and proofs.
The compiler requires of a session's annotation: the kinds of rounds run "local, then shared, then
local", and a component that is not sent is empty (Iop/BatchFmt.lean: `RoundSplits.Fmt`; a clause of
`FitK`, CompileK/Main.lean). A session of the object is: the preamble of a request (local rounds),
then the test for linear constraints for a batch.
An annotation runs from the phase ph to ph' (`RoundSplits.Runs`, Ior/BatchFmtApp.lean) if from ph on every
round has a format and a component that is not sent is empty, and the rounds end in ph'; a chain of
annotated links runs (`ChainA.Runs`, Cb/Ld/LdLinChainBFmt.lean) link by link, along some phases
between. The phases (`FPhase`, Iop/BatchFmt.lean) are: before the first round; in the local rounds
before the shared ones; in the shared rounds; in the local rounds after them.

Main names:
  `Spec.ldOnT_runs`: the batch test's term (Cb/Obj/LdObjectOnBTerm.lean: `termT`) runs from a phase
    before the shared rounds to ph', if its closing runs from "in the shared rounds" to ph'.
  `Spec.ldPlan_runs`: the closing at the plan (Cb/Ld/LdBatchBlocksPlan.lean: `cZA`;
    Cb/Ld/LdBatchPlanLin.lean: `QA`): a step without rounds; the first test once, by the shared
    part: shared rounds; the second test in every slot: local rounds after the shared ones; then
    the rest, which has to run from there (so: local rounds only).
  `consLo_runs`, `tcNil_runs`: rules for a rest: a test in every slot, then a plan that runs from
    the local rounds after the shared ones; "nothing is left".
  `Spec.ldObjT_fmt`: the session of `T.obj` has the format, if the closing cZ runs from "in the
    shared rounds".
  `Spec.ldObjP_fmt`: at the plan (`P : LdObjP`, Cb/Obj/LdObjectPlan.lean): from `P.Hyp L`, if the
    rest's annotated chain cA' runs from "in the local rounds after the shared ones".
  `Spec.ldOnT_runs` and `Spec.ldPlan_runs` also require that the index code has a position
    (`Nonempty (Fin O.Cf.C₀.n)`, `Nonempty ι`).

Limits: this file does not say that a given rest runs so (a rest of tests in every slot does:
`consLo_runs`, `tcNil_runs`, `Iop.fmtRuns_local`).
Declared, a point that the format decides and a write-up of ours (lean/CREDITS.md) leaves
open. The write-up has all splittings of a closing step before its tests. If the shared part
splits and every slot splits, that order would put a slot's scalar between shared rounds, which the
format excludes. So whatever a slot does after the joining round (its splitting too) stands behind
all rounds of the shared part, before that slot's own tests.
With nothing merged, the last local round before the shared ones carries the answers of the slot's
own family and no verifier message of weight, and the first shared round carries no prover message
and the shared point; a text that lets the first shared round carry a part of each instance's prover
counts the same thing once.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Obj.LdObjectPlan
import Cb.Ld.LdLinChainBFmt
import Cond.ObjBits

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldOnT_runs : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)]
      (on0 : (O.P.D.X.Row → Fin O.Cf.C₀.n → E) → O.P.D.X.Rec → Prop) (Sn : O.toC.P.Snd)
      (qa : Finset O.toC.P.Ea.Pos → Prop) (εf N : ℕ) (VT : JV N LdLinP.JT)
      (cZ : ChainV Unit N (O.toC.P.V6 Sn qa N) VT) (d : O.toC.P.W0) (d₀ : O.P.W0) (ph ph' : FPhase),
    ph.afterLo = .loc → cZ.forget.Runs .shr ph' → (O.termT on0 Sn qa εf N cZ d d₀).A.Runs ph ph'

def ldObjT_fmt : Prop :=
  ∀ (T : LdObjT F E) (r : T.obj.Cf.conf.Rec) (ph' : FPhase),
    T.cZ.forget.Runs .shr ph' → (T.obj.subs.obj r).onlineBatch.ann.Fmt

def ldObjP_fmt : Prop :=
  ∀ (P : LdObjP F E) (L : ℕ) (r : P.toT.obj.Cf.conf.Rec) (ph' : FPhase),
    P.Hyp L → P.cA'.Runs .aft ph' → (P.toT.obj.subs.obj r).onlineBatch.ann.Fmt

end

/-- The closing at the plan. States, under the hypotheses below: it runs from "in the shared rounds"
to ph', if cA' runs from "in the local rounds after the shared ones" to ph'. -/
def ldPlan_runs (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ]
    [Fintype J] [Fintype Y] : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPl C) (T : LdLinPlT p)
      (cA' : ChainA Unit (p.S₂.jointCf T.Q'.base) ldTrivJ)
      (same' : cA'.forget = T.Q'.c) (ph' : FPhase),
    cA'.Runs .aft ph' → (C.cZA (T.QA cA' same') T.fq).Runs .shr ph'

end Spec

theorem ldPlan_runs (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ]
    [Fintype J] [Fintype Y] : Spec.ldPlan_runs E ι κ J Y := by
  intro C p T cA' same' ph' h
  refine chainA_runs_append _ _ _ _ _ _ .shr .shr ph'
    ((ChainA.runs_one _ _ _).2 (fmtRuns_nil _ .shr)) ?_
  refine chainA_runs_append _ _ _ _ _ _ .shr .shr ph'
    ((ChainA.runs_one _ _ _).2 (fmtRuns_shared _).1) ?_
  refine chainA_runs_append _ _ _ _ _ _ .shr .aft ph' ((ChainA.runs_one _ _ _).2 ?_) h
  have h2 := fmtRuns_local (T.D₂.link T.Q'.base T.d₂ T.d₂').R.shape .shr
  have hne : (T.D₂.link T.Q'.base T.d₂ T.d₂').R.shape ≠ [] := List.cons_ne_nil _ _
  rw [if_neg hne] at h2
  exact h2

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldOnT_runs : Spec.ldOnT_runs F E := by
  intro O _ on0 Sn qa εf N VT cZ d d₀ ph ph' hph hc
  show (O.toC.P.linCV Sn qa N on0 εf cZ d).a.Runs ph ph'
  unfold LdLinP.linCV
  rw [chainV_link, chainV_forget_append, ldLinV_forget]
  exact chainA_runs _ _ _ _ _ ph ph'
    (chainA_runs_append _ _ _ _ _ _ ph .shr ph'
      (ldLinCB_runs _ _ _ _ _ O.toC.P on0 Sn εf N ph hph) hc)

theorem ldObjT_fmt : Spec.ldObjT_fmt F E := by
  intro T r ph' h
  refine online_fmt _ _ _ _ T.obj.subs.req T.obj.subs.linOn ph' ?_
  refine ldOnT_runs F E T.on.ol T.onB T.SnB T.qaB T.εfB T.N T.VT T.cZ T.dB T.dB₀ _ ph' ?_ h
  split <;> rfl

theorem ldObjP_fmt : Spec.ldObjP_fmt F E := by
  intro P L r ph' h hA
  obtain ⟨-, -, -, hV4, -⟩ :=
    ldLinVL_all E _ _ _ _ P.on.ol.toC P.pB P.TB P.N P.q₀B P.bB' P.tie' P.cA' P.same' P.x₀ P.y₀ P.QV'
      P.SnB P.qaB P.baB h.r.shared h.r.restB h.r.saysAB h.test₁B h.test₂B h.r.leftV h.r.tieC
      h.r.qaOK h.r.needNA h.r.needNW h.r.needNU h.r.needNO
  refine ldObjT_fmt F E P.toT r ph' ?_
  show P.cZ.forget.Runs .shr ph'
  rw [show P.cZ.forget = _ from hV4]
  exact ldPlan_runs E _ _ _ _ P.on.ol.toC P.pB P.TB P.cA' P.same' ph' hA

end
/-- A test in every slot, then a plan that runs from the local rounds after the shared ones (`h`),
runs from there too. -/
theorem consLo_runs {E : Type} [Field E] [Fintype E] {S : Sig E} {E₀ : ExtSpec} {Wp : Type}
    (D : LdRunD S) (QA : LdTcA (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp)
    (ph' : FPhase) (h : QA.cA.Runs .aft ph') :
    (LdTcA.consLo D QA d d').cA.Runs .aft ph' := by
  refine chainA_runs_append _ _ _ _ _ _ .aft .aft ph' ((ChainA.runs_one _ _ _).2 ?_) h
  have h2 := fmtRuns_local (D.link QA.Q.base d d').R.shape .aft
  have hne : (D.link QA.Q.base d d').R.shape ≠ [] := List.cons_ne_nil _ _
  rw [if_neg hne] at h2
  exact h2

theorem tcNil_runs {E : Type} [Field E] (S : Sig E) (E₀ : ExtSpec) (Wp : Type)
    (w₀ : S.Wit × Wp) (ph : FPhase) :
    (LdTcA.nil S E₀ Wp w₀).cA.Runs ph ph :=
  (ChainA.runs_one _ _ _).2 (fmtRuns_nil _ ph)

end Cb
