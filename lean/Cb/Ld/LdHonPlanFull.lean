-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdHonPlanFull.lean: the term of the test at N instances is in order (`LinBT.OK`) at the
object's data with the session's four whole tests at the full list of errors (`R.fullB`,
Cb/Ld/LdHonPlanDef.lean), from `(R.toLdObjD.std R.Y).HypRestH L`, `R.Y.Hyp`, `R.HypPl` and "each of
the four tests, its errors overwritten, is in order" (`D.full.OK`).

Statements (in `Cb.Spec`) and proofs. Generic. Nothing assumed beyond the hypotheses of the
statements and whatever the arguments hold as proofs. The test at N instances is the sub-protocol
`linOn` of `SubsR` (Hiop/RecSubs.lean). The full list (`Err.full`, Cb/Gen/FullErr.lean) has, for
each round, the number of all values of that round's verifier message: as a probability, the error
1.

Main names:
  `Spec.ldHonF_pl`: `R.HypPl` → `R.fullB.HypPl`: the 36 conditions on places, numbers and forms
    read no error: each field is R's own, by unfolding.
  `Spec.ldHonF_on`: `(R.toLdObjD.std R.Y).HypRestH L`, `R.Y.Hyp`, `R.HypPl`, `R.TB₀.D₁.full.OK`,
    `R.TB₀.D₂.full.OK`, `R.TB₀.D₃.full.OK`, `R.XB.run.full.OK` ⇒ `R.fullB.HypOnR L`.
  `Spec.ldHonF_term`: the premises of `Spec.ldHonF_on` ⇒ the term of the test at N instances at
    `R.fullB.toPp`, at that object's own parameters, is `OK`.

Why: `D.full.OK` asks nothing on agreement of codes where D is a tower below the Johnson radius
(`ldRunD_fullOK`, Cb/Gen/FullErrTow.lean).

Limits: the conclusion speaks of `R.fullB`'s term, not of R's: that the two agree off their errors,
and so that R's own term has the honest items, is Cb/Ld/LdHonPlanEq.lean with Cb/Ld/LdHonOnB.lean.
This file says nothing on the chance of a cheating prover at R's own term, nor in a round of the
four tests' `D.T`: `LinBT.OK` (Cb/Obj/LdObjectOnB.lean), which `Spec.ldHonF_term` concludes of the
term at `R.fullB.toPp`, has the clauses fits, and know at that term's own list of errors, in which
these rounds have the full list; `R.fullB.HypOnR L`, which `Spec.ldHonF_on` concludes, has `OK` of
the four tests at the full list and, as rest0, `HypRestH L` whole (Cb/Ld/LdHonOff.lean), all handed
on from the premises. It does not say that the premises hold anywhere.



Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdHonPlanDef
import Cb.Ld.LdHonPlanOn

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldHonF_pl : Prop := ∀ R : LdObjRp F E, R.HypPl → R.fullB.HypPl

def ldHonF_on : Prop :=
  ∀ (R : LdObjRp F E) (L : ℕ), (R.toLdObjD.std R.Y).HypRestH L → R.Y.Hyp → R.HypPl →
    R.TB₀.D₁.full.OK → R.TB₀.D₂.full.OK → R.TB₀.D₃.full.OK → R.XB.run.full.OK → R.fullB.HypOnR L

def ldHonF_term : Prop :=
  ∀ (R : LdObjRp F E) (L : ℕ), (R.toLdObjD.std R.Y).HypRestH L → R.Y.Hyp → R.HypPl →
    R.TB₀.D₁.full.OK → R.TB₀.D₂.full.OK → R.TB₀.D₃.full.OK → R.XB.run.full.OK →
    (R.fullB.toPp.D.on.ol.termT R.fullB.toPp.D.onB R.fullB.toPp.D.SnB R.fullB.toPp.D.qaB
      R.fullB.toPp.D.εfB R.fullB.toPp.D.N R.fullB.toPp.cZ R.fullB.toPp.D.dB R.fullB.toPp.D.dB₀).OK

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldHonF_pl : Spec.ldHonF_pl F E := fun _ h =>
  { q₀is := h.q₀is, entAt := h.entAt, plain := h.plain, kept := h.kept, kIs := h.kIs,
    noPad := h.noPad, restIs := h.restIs, plW := h.plW, plC := h.plC, plR := h.plR,
    nowX := h.nowX, kpX := h.kpX, needA := h.needA, needW := h.needW, needU := h.needU,
    needO := h.needO, shared := h.shared, plainB := h.plainB, keptB := h.keptB, kIsB := h.kIsB,
    noPadB := h.noPadB, abRel := h.abRel, abRelR := h.abRelR, plRB := h.plRB,
    restIsB := h.restIsB, restVal := h.restVal, plSB := h.plSB, nowXB := h.nowXB, kpXB := h.kpXB,
    q₀Be := h.q₀Be, qaOK := h.qaOK, oneN := h.oneN, needNA := h.needNA, needNW := h.needNW,
    needNU := h.needNU, needNO := h.needNO }

theorem ldHonF_on : Spec.ldHonF_on F E := fun R _ h0 hY hp t1 t2 t3 t4 =>
  { rest0 := h0, sndOK := hY, pl := ldHonF_pl F E R hp, test₁B := t1, test₂B := t2,
    test₃B := t3, test₄B := t4 }

theorem ldHonF_term : Spec.ldHonF_term F E := fun R L h0 hY hp t1 t2 t3 t4 =>
  ldHonP_termD F E R.fullB.toPp L
    (ldHonRp_on F E R.fullB L (ldHonF_on F E R L h0 hY hp t1 t2 t3 t4))

end
end Cb
