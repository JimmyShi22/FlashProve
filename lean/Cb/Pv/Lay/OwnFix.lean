-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Pv/Lay/OwnFix.lean: in the chain of a layers' sub-proof's own rounds, filled from the records
(Cb/Pv/Lay/OwnAll.lean), every sumcheck leaves out a coefficient that may be left out.

A short sumcheck's verifier completes each message from the coefficients that are sent. Where the
pick of the coefficient that is left out is lawful it refuses nothing, and what it puts out can be
written out (`Ch.FixOK`, `Ch.tot`, Cb/Pv/Att/ChainVal.lean).

Main names:
  `ProdL.pick_okS`, `MergeL.pick_okS`: the picks of a product layer's sumcheck and of the merge,
    read as values of Cb/Pv/Lay/Sum.lean, are lawful.
  `LayV.fixOK`, `LayVF.fixOK`, `LayVO.fixOK`, `LayVOF.fixOK`: `Ch.FixOK` of the chain, if the pick
    F4 of the batched sumcheck, which is a letter, is lawful.

Limits: that F4 is lawful is a premise. Nothing is said on the honest prover, on completeness or
on zero knowledge.
-/
import Cb.Pv.Lay.OwnAll
import Cb.Pv.Att.ChainVal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR TWhole Johnson.L5.Layers Cb.Pv.Att

variable {E : Type} [Field E] [Fintype E] {M : Type}

/-- The pick of a product layer's sumcheck, read as a value of Cb/Pv/Lay/Sum.lean, is lawful. -/
theorem ProdL.pick_okS (L : ProdL E) :
    ∀ st, HFixs.OK (L.toSum.T.par.vars st) (F₀ L.toSum.T.par st) :=
  F₀_ok L.toSum.T.par L.eq0

/-- The same for the merge. -/
theorem MergeL.pick_okS (L : MergeL E) (st : L.St) :
    HFixs.OK (L.toSum.T.par.vars st) (pick (L.toSum.T.par.vars st)) :=
  L.pick_ok st

namespace LayV
variable {X : Type} (V : LayV E M X)

/-- Every sumcheck of the chain has a lawful pick, if the batched sumcheck's is lawful. -/
theorem fixOK (h4 : ∀ st, HFixs.OK (V.In.toSum.T.par.vars st) (V.F4 st)) : V.toTail.ch.FixOK :=
  ⟨V.G.R.L.pick_okS, V.Rw.tok.pick_ok, V.Tm.pick_ok, h4, V.Ft.Gp.pick_okS, V.Ft.Rt.L.pick_okS,
    V.Ft.Wt.L.pick_okS, trivial⟩

end LayV

namespace LayVF
variable {X : Type} (V : LayVF E M X)

theorem fixOK (h4 : ∀ st, HFixs.OK (V.In.toSum.T.par.vars st) (V.F4 st)) : V.toTail.ch.FixOK :=
  ⟨V.G.R.L.pick_okS, V.Rw.tok.pick_ok, V.Tm.pick_ok, h4, V.Ft.Gp.pick_okS, V.Ft.Rt.L.pick_okS,
    V.Ft.Wf.L.pick_okS, trivial⟩

end LayVF

theorem LayVO.fixOK {X : Type} (A : LayVO E M X)
    (h4 : ∀ st, HFixs.OK (A.V.In.toSum.T.par.vars st) (A.V.F4 st)) : A.toOwn.ch.FixOK :=
  A.V.fixOK h4

theorem LayVOF.fixOK {X : Type} (A : LayVOF E M X)
    (h4 : ∀ st, HFixs.OK (A.V.In.toSum.T.par.vars st) (A.V.F4 st)) : A.toOwn.ch.FixOK :=
  A.V.fixOK h4

end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.LayVO.fixOK
#print axioms Cb.Pv.Lay.LayVOF.fixOK
