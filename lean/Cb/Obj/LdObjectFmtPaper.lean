-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectFmtPaper.lean: the session of the object at the plan with a splitting has the format
that the compiled scheme can carry, under `P.Hyp L` and a condition on the rest of the closing.

Book-keeping for the compiled scheme: the kind of a round and its phase fix the format of the
verifier's Fiat-Shamir query (Iop/BatchFmt.lean). This file is about the order of the kinds in a
session: in a shared round the verifier message is one for all slots, in a local round each slot
has its own (Iop/Batch.lean).

Theorems. The analogue, for the plan with a splitting (`LdObjPp`, Cb/Obj/LdObjectPlanPaper.lean),
of `Spec.ldObjP_fmt`, Cb/Obj/LdObjectFmt.lean (the plan without a splitting). Generic.
What "runs" means (`RoundSplits.Runs`, `ChainA.Runs`) and the phases (`FPhase`) are told in the head of
Cb/Obj/LdObjectFmt.lean; what it says holds here too.

Main names:
  `ldPlanP_runs`: the closing for a batch at the plan with a splitting (step; front; two shared
    tests; a test in every slot; the rest) runs from "in the shared rounds", if the rest's annotated
    chain cA' runs from "in the local rounds after the shared ones", and the index code has a
    position (`Nonempty ι`).
  `ldObjPp_fmt`: `P.Hyp L` and that condition on `P.cA'` ⇒ the session of `P.toT.obj` has the
    format.

Why `P.Hyp L` stands among the premises of facts on format and countability: the online closing
`P.cZ` is the term with its honest side; that, its honest side forgotten, it is the plan's
annotated chain (`ldObjPp_forget`) is an equation between terms that is proved from the plan's
conditions (`Cb.ldLinPV_std`), not one that holds by definition. So format and countability of
`P.toT` are shown here (countability: `ldObjPp_ctbT`, Cb/Obj/LdObjectCtbPaper.lean, which also has
the premise `P.CtbPp`) for objects that meet `P.Hyp L` only. Cb/Ld/LdHonSide.lean proves the
equation (`ldHon_forget`), and, under the same condition on `P.cA'`, that the closing runs so
(`ldHon_runs`), and countability from `P.CtbPp` (`ldHon_ctbT`), all without `P.Hyp L`.

Limits: this file does not say that `P.Hyp L` can be met. On security: the records that its
statements assume have among their fields `know`, `exact` (`IOR.GoodT`, Ior/KnowCollGood.lean),
inside `P.Hyp L` (Cb/Obj/LdObjectPlanPaper.lean). This file's statements conclude only `Runs`,
`RoundSplits.Fmt` and one equation of chains.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectPlanPaper
import Cb.Obj.LdObjectFmt

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

theorem front_runs {E : Type} [Field E] [Fintype E] {S : Sig E} {E₀ : ExtSpec} {Wp : Type} :
    ∀ {x y : FSt S E₀ Wp Unit} (p : Front x y), (Front.cA true p).Runs .shr .shr
  | _, _, .nil x => by
      rw [Front.cA]
      exact (ChainA.runs_one _ _ _).2 (fmtRuns_nil _ .shr)
  | _, _, .step p z f g m back => by
      rw [Front.cA]
      exact (ChainA.runs_snoc _ _ _ _).2 ⟨.shr, front_runs p, fmtRuns_nil _ .shr⟩
  | _, _, .bat B iB Sb sl Z St₀ A₀ p => by
      rw [Front.cA]
      refine (ChainA.runs_snoc _ _ _ _).2 ⟨.shr, front_runs p, ?_⟩
      unfold Front.md
      rw [if_pos rfl]
      exact (fmtRuns_shared _).1
  | _, _, .split G₁ G₂ k St₁ St₂ sl₁ sl₂ St₀ A₀ Rs dRs p => by
      rw [Front.cA]
      refine (ChainA.runs_snoc _ _ _ _).2 ⟨.shr, front_runs p, ?_⟩
      unfold Front.md
      rw [if_pos rfl]
      exact (fmtRuns_shared _).1

theorem ldPlanP_runs (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ]
    [Fintype J] [Fintype Y] (C : LdLinC E ι κ J Y) (p : LdLinPp C) (T : LdLinPpT p)
    (cA' : ChainA Unit (p.S₃.jointCf T.Q'.base) ldTrivJ) (same' : cA'.forget = T.Q'.c)
    (ph' : FPhase) (h : cA'.Runs .aft ph') :
    (C.cZA (T.QA cA' same') (C.fqP T.fa)).Runs .shr ph' := by
  refine chainA_runs_append _ _ _ _ _ _ .shr .shr ph'
    ((ChainA.runs_one _ _ _).2 (fmtRuns_nil _ .shr)) ?_
  refine chainA_runs_append _ _ _ _ _ _ .shr .shr ph' (front_runs T.front) ?_
  refine chainA_runs_append _ _ _ _ _ _ .shr .shr ph'
    ((ChainA.runs_one _ _ _).2 (fmtRuns_shared _).1) ?_
  refine chainA_runs_append _ _ _ _ _ _ .shr .shr ph'
    ((ChainA.runs_one _ _ _).2 (fmtRuns_shared _).1) ?_
  refine chainA_runs_append _ _ _ _ _ _ .shr .aft ph' ((ChainA.runs_one _ _ _).2 ?_) h
  have h2 := fmtRuns_local (T.D₃.link T.Q'.base T.d₃ T.d₃').R.shape .shr
  have hne : (T.D₃.link T.Q'.base T.d₃ T.d₃').R.shape ≠ [] := List.cons_ne_nil _ _
  rw [if_neg hne] at h2
  exact h2

/-- Under `h`: the online closing, its honest side forgotten, is the annotated chain of the plan. -/
theorem ldObjPp_forget {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (P : LdObjPp F E) (L : ℕ) (h : P.Hyp L) :
    P.cZ.forget = P.on.ol.toC.cZA (P.TB.QA P.cA' P.same') (P.on.ol.toC.fqP P.TB.fa) := by
  obtain ⟨-, -, -, v4, -⟩ := ldLinPV_std P.Y.Fp E _ _ _ _ P.on.ol.toC P.pB P.TB P.N P.q₀B P.bB'
    P.tie' P.x₀ P.y₀ P.cA' P.same' P.xB P.xC P.yE P.QV' P.Y.TB P.Y.LWB P.Y.LUB P.Y.LOB P.Y.tWB
    P.Y.tUB P.Y.tOB P.n₀B P.qaB P.baB P.onB P.εfB P.sh₀ P.x₄ P.y₄ h.r.shared h.r.plainB h.r.keptB
    h.r.restB h.r.saysAB h.test₁B h.test₂B h.test₃B h.r.leftV h.r.tieC h.r.qaOK h.r.needNA
    h.r.needNW h.r.needNU h.r.needNO h.r.sndOK.on.places h.r.sndOK.on.okW h.r.sndOK.on.okU
    h.r.sndOK.on.okO h.r.kIsB h.r.noPadB
  exact v4

theorem ldObjPp_runs {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (P : LdObjPp F E) (L : ℕ) (ph' : FPhase) (h : P.Hyp L) (hA : P.cA'.Runs .aft ph') :
    P.toT.cZ.forget.Runs .shr ph' := by
  show P.cZ.forget.Runs .shr ph'
  rw [ldObjPp_forget P L h]
  exact ldPlanP_runs E _ _ _ _ P.on.ol.toC P.pB P.TB P.cA' P.same' ph' hA

theorem ldObjPp_fmt {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E]
    [Algebra F E] (P : LdObjPp F E) (L : ℕ) (r : P.toT.obj.Cf.conf.Rec) (ph' : FPhase)
    (h : P.Hyp L) (hA : P.cA'.Runs .aft ph') :
    (P.toT.obj.subs.obj r).onlineBatch.ann.Fmt :=
  ldObjT_fmt F E P.toT r ph' (ldObjPp_runs P L ph' h hA)

end Cb
