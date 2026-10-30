-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Lay/OwnTot.lean: the verifier of the chain of a layers' sub-proof's own rounds, filled from
the records (Cb/Pv/Lay/OwnAll.lean), refuses nothing, if the batched sumcheck leaves out the
linear coefficient.

Knowledge soundness alone does not shut out a verifier that refuses everything. A short sumcheck's
verifier completes each message from the coefficients that are sent; where the pick of the
coefficient that is left out is lawful it refuses nothing (Cb/Pv/Att/ChainVal.lean).
Cb/Pv/Lay/OwnFix.lean shows six of the seven picks lawful and leaves the seventh, a letter of the
record, as a premise. Here that premise is paid for the programs' choice.

Main names:
  `InnL.pick_okS`: for the batched sumcheck, read as a value of Cb/Pv/Lay/Sum.lean, the pick
    `pick` (Cb/Pv/Lay/Merge.lean) is lawful: the linear coefficient in each plain variable, the
    constant one in the further variable.
  `LayVO.PickIs`, `LayVOF.PickIs`: the record's letter F4 is that pick.
  `LayVO.fixOK_pick`, `LayVOF.fixOK_pick`: then every sumcheck of the chain has a lawful pick.
  `LayVO.tot`, `LayVOF.tot`: then the chain's verifier puts out a statement on every transcript
    (`Tot`, Cb/G9/Tot.lean), namely `Ch.val`.
  `LayTail.run_st3`: at the last statement of a run (`Ch.run`, Cb/Pv/Att/ChainRun.lean) the state
    inside the output of the sumcheck of the terms is the one that the letters' claim names at the
    statement before it. The claims that are owed at the chain's end read that state.

Limits: a verifier that refuses nothing tests nothing: all that the chain's knowledge soundness
gives lies in its last claim (`Ch.Last`), which whoever follows must test (Cb/Pv/Att/Chain.lean,
Cb/Pv/Lay/Own.lean). `PickIs` is a premise on the record; that it is the programs' choice is by
reading. The test on the coefficient drawn in the sumcheck of the terms is not among the chain's
rounds: the reduction with that test behind it does refuse (`tested`, Cb/Pv/Lay/OwnTest.lean).
`LayTail.run_st3` is of the third sumcheck alone and at the letters. Nothing is said on the honest
prover, on completeness or on zero knowledge.
-/
import Cb.Pv.Lay.OwnFix
import Cb.Pv.Att.ChainLast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR TWhole TWhole.G9 Johnson.L5.Layers Cb.Pv.Att

variable {E : Type} [Field E] [Fintype E] {M : Type}

/-- In the batched sumcheck all variables but the further one are plain: the pick that leaves out
the linear coefficient (the constant one in the further variable) is lawful. -/
theorem InnL.pick_okS (L : InnL E) (st : L.St) :
    HFixs.OK (L.toSum.T.par.vars st) (pick (L.toSum.T.par.vars st)) :=
  Cb.Pv.Lay.pick_ok _ fun v hv => by
    rcases mem_snoc L.toSum.T.fmt (L.toSum.T.dat st) (pDummy E L.toSum.T.DY)
      (pDummyD E L.toSum.T.DY) v hv with h1 | h1
    · exact plain_vars L.k (fun _ => 2) (fun _ => by norm_num) v h1
    · rw [h1]
      exact Or.inl (mon0_dummy L.toSum.T.DY)

/-- The record's pick for the batched sumcheck is that one. -/
def LayVO.PickIs {X : Type} (A : LayVO E M X) : Prop :=
  A.V.F4 = fun st => pick (A.V.In.toSum.T.par.vars st)

def LayVOF.PickIs {X : Type} (A : LayVOF E M X) : Prop :=
  A.V.F4 = fun st => pick (A.V.In.toSum.T.par.vars st)

theorem LayVO.fixOK_pick {X : Type} (A : LayVO E M X) (h : A.PickIs) : A.toOwn.ch.FixOK :=
  A.fixOK fun st => by
    rw [show A.V.F4 = _ from h]
    exact A.V.In.pick_okS st

theorem LayVOF.fixOK_pick {X : Type} (A : LayVOF E M X) (h : A.PickIs) : A.toOwn.ch.FixOK :=
  A.fixOK fun st => by
    rw [show A.V.F4 = _ from h]
    exact A.V.In.pick_okS st

/-- With that pick the chain's verifier refuses nothing: on every transcript it puts out a
statement. -/
theorem LayVO.tot {X : Type} (A : LayVO E M X) (h : A.PickIs) (Ex : ExtSpec) :
    Tot (A.toOwn.ch.R Ex).red (A.toOwn.ch.val Ex) :=
  Ch.tot Ex A.toOwn.ch (A.fixOK_pick h)

theorem LayVOF.tot {X : Type} (A : LayVOF E M X) (h : A.PickIs) (Ex : ExtSpec) :
    Tot (A.toOwn.ch.R Ex).red (A.toOwn.ch.val Ex) :=
  Ch.tot Ex A.toOwn.ch (A.fixOK_pick h)

/-! ### At a run, the state inside the terms' output -/

/-- At the last statement of a run, the state that stands in the output of the sumcheck of the
terms is the one that the letters' claim names at the statement before that sumcheck. -/
theorem LayTail.run_st3 {X : Type} (T : LayTail E M X) (x : X) (ts : T.ch.Trs) :
    (T.ch4.back (T.ch.run x ts)).2.st =
      (T.s3.cl (T.ch4.back (T.ch.run x ts)).1.1 (T.ch4.back (T.ch.run x ts)).1.2).2 := by
  obtain ⟨t0, t1, t2, t3, t4, t5, t6, t7⟩ := ts
  show (T.ch4.back (T.ch4.run _ t7)).2.st =
    (T.s3.cl (T.ch4.back (T.ch4.run _ t7)).1.1 (T.ch4.back (T.ch4.run _ t7)).1.2).2
  rw [Ch.back_run]
  rfl

end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.LayTail.run_st3
#print axioms Cb.Pv.Lay.InnL.pick_okS
#print axioms Cb.Pv.Lay.LayVO.fixOK_pick
#print axioms Cb.Pv.Lay.LayVO.tot
#print axioms Cb.Pv.Lay.LayVOF.tot
