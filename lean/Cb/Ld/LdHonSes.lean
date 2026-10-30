-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdHonSes.lean: the session's clause of the honest half, at the object at the technical
report's plan (`R : LdObjRp`, Cb/Obj/LdObjectPpRows.lean). All honest items of the test at N
instances hold
at the object's own term (`R.toPp.toT.linB`), from `(R.toLdObjD.std R.Y).HypRestH L`, `R.Y.Hyp`,
`R.HypPl` and "the session's four whole tests, their errors overwritten by the full list, are in
order" (`D.full.OK`).

One statement (`Cb.Spec.ldHonS_okh`), one corollary, proofs: a join of three files. Generic: a
variable R. Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold
as proofs.
The honest half is `SubsR.HypH` (Hiop/RecBuild.lean): the parameter lists of the sub-protocols (wf,
linOff, link, req, linOn) without their items on knowledge soundness, which are in `SubsR.HypK`, and
the two clauses fitOff, fitOn. Its clause linOn, the session's, is `LinBListR` (Hiop/RecSubs.lean):
the parameter list of the IOPP for the constraint relation, at most N instances: all items but
knowledge soundness. The test at N instances is the sub-protocol `linOn` of `SubsR`
(Hiop/RecSubs.lean). The honest items are the clauses of `LinBT.OKH` (Cb/Ld/LdHonOnB.lean).

Main names:
  `Spec.ldHonS_list`: the premises of `Spec.ldHonS_okh` ⇒ `Hiop.LinBListR` at `R.toPp.toT.obj`'s own
    linOn, hLinOn, N, numbers; the bound on what the test reads is monotone; what it reads lies
    within what it is given, which meets the bound.

Why: (1) Cb/Ld/LdHonPlanFull.lean: at `R.fullB` (another object's data: the four tests overwritten)
the theorems of Cb/Ld/LdHonPlanOn.lean apply whole: the test's term at `R.fullB`'s closing is in
order (`LinBT.OK`). (2) Cb/Ld/LdHonPlanEq.lean: `R.fullB`'s closing and R's own agree off their
errors (`R.fullB.toPp.cZ.full = R.toPp.cZ.full`). (3) Cb/Ld/LdHonOnB.lean: the honest items pass
along such an equation. The conclusion speaks of R's own term: `R.fullB` does not occur in the
statement.

Limits: `D.full.OK` says of a whole test D all that `D.OK` says but the knowledge soundness of a
test that has a round. For a test without a round the plain implication between the relations stays;
the bound on lists, a fact on words, is kept (see the heads of Cb/Gen/FullErr.lean,
Cb/Gen/FullErrTow.lean). `D.full.OK` is had from `LdRunD.PreJD` (Cb/Gen/FullErrTow.lean: for D a
tower below the Johnson radius) where `D.OK` needs agreement of codes. So the clause linOn of
`Hiop.SubsR.HypH`, and the two clauses that the clause fitOn draws from the session's side, do not
depend on the agreement that `D.OK` of the session's four whole tests needs. This file says nothing
on the chance of a cheating prover.
This file does not say that the premises hold anywhere.
`T.OKH` leaves out `T.OK`'s
clauses fits and know. This file says nothing on the value of any number.

Terms: lean/GLOSSARY.md.
"The technical report": this protocol's technical report (lean/CREDITS.md).
-/
import Cb.Ld.LdHonPlanEq
import Cb.Ld.LdHonPlanFull
import Cb.Ld.LdHonOnB

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- All honest items of the test at N instances, at the object's own term
(`R.toPp.toT.linB.OKH`). -/
def ldHonS_okh : Prop :=
  ∀ (R : LdObjRp F E) (L : ℕ), (R.toLdObjD.std R.Y).HypRestH L → R.Y.Hyp → R.HypPl → R.TB₀.D₁.full.OK → R.TB₀.D₂.full.OK → R.TB₀.D₃.full.OK → R.XB.run.full.OK → R.toPp.toT.linB.OKH

def ldHonS_list : Prop :=
  ∀ (R : LdObjRp F E) (L : ℕ), (R.toLdObjD.std R.Y).HypRestH L → R.Y.Hyp → R.HypPl →
    R.TB₀.D₁.full.OK → R.TB₀.D₂.full.OK → R.TB₀.D₃.full.OK → R.XB.run.full.OK →
    LinBListR R.toPp.toT.obj.subs.on R.toPp.toT.obj.subs.linOn R.toPp.toT.obj.subs.hLinOn
      R.toPp.toT.obj.subs.N R.toPp.toT.obj.nums.linOn ∧
    (∀ U V, V ⊆ U → R.toPp.toT.linB.qi U → R.toPp.toT.linB.qi V) ∧
    (∀ ρ,
      R.toPp.toT.linB.qi (R.toPp.toT.linB.R.given ρ ∅) ∧
      R.toPp.toT.linB.R.extReads ρ ⊆ R.toPp.toT.linB.R.given ρ ∅)

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

set_option maxHeartbeats 1000000 in
theorem ldHonS_okh : Spec.ldHonS_okh F E := fun R L h1 h2 h3 t1 t2 t3 t4 =>
  ldHonB_carry F E R.toPp.D.on.ol R.toPp.D.onB R.toPp.D.SnB R.toPp.D.qaB R.toPp.D.εfB R.toPp.D.N
    R.toPp.QV'.VT R.toPp.cZ R.fullB.toPp.cZ R.toPp.D.dB R.toPp.D.dB₀ (ldHonEq_obj F E R).symm
    (ldHonF_term F E R L h1 h2 h3 t1 t2 t3 t4)

theorem ldHonS_list : Spec.ldHonS_list F E := fun R L h1 h2 h3 t1 t2 t3 t4 =>
  have h := ldHonS_okh F E R L h1 h2 h3 t1 t2 t3 t4
  ⟨ldHonB_list F E _ _ _ h, h.mono, h.reads⟩

end
end Cb
