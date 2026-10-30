-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/FullShapeAtName.lean: the test `Desc.K14.Law.fullShapeB`
(Johnson/Desc/Sound/PlanAsk.lean) at the linear shape of the closed letters of the head's law,
`(At.P13 Zp).lin`: it accepts wherever the value is laid in scope and the test that holds the made
plan to the written one accepts.

Row or tool. One closed fact with its negative tests, and the law in scope by rewriting through a
named tie. A payer for a premise of another law.

The test's argument, its written term and its tie. `(At.P13 Zp).lin` is `Zp.first.lin`, the linear
shape as it is read back, by definition (`K13.whereOf`, Johnson/Desc/ProofFile/Lot/K13.lean).
Written term: `proofSizedFull.batch.shape` (Johnson/Desc/Ok/PlanWritten/SizedLit.lean). Tie: the
second equation of `first_written_in_scope` (Johnson/Goal/Numbers/MadeInScope.lean).

The premise beyond scope, the files read, and the value laid. One: `madePinnedAt … = true`: the
accept of a test that the verifier's entry tests for the proof file ask once they are thirteen.

What is here.
  `fullShape_written`: the test accepts at the written linear shape.
  `fullShape_rejects`: negative tests, one for each of its three clauses: with one matrix row more;
    with the lower number of column bits one higher; with the index's number of variables one
    higher.
  `fullShape_at_name`.
By evaluations in Lean's kernel (`decide +kernel`): the first two.

Limits. Nothing in this file says that `madePinnedAt` accepts at any files. Nothing on soundness.


-/
import Johnson.P5J.LettersAt2
import Johnson.P5J.LaidOpens
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Desc.Sound.PlanAsk

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes OnBytes.Params
open VerifiableInference.PlanWritten (madePinnedAt proofSizedFull)
open VerifiableInference.PlanWritten.Joined (first_written_in_scope)
open Desc.K14.Law (fullShapeB)

set_option maxRecDepth 1000000 in
/-- **The test accepts at the written linear shape.** -/
theorem fullShape_written : fullShapeB proofSizedFull.batch.shape = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **Negative tests**, one for each clause. -/
theorem fullShape_rejects :
    fullShapeB { proofSizedFull.batch.shape with
        matrixRows := proofSizedFull.batch.shape.matrixRows + 1 } = false ∧
      fullShapeB { proofSizedFull.batch.shape with kLo := proofSizedFull.batch.shape.kLo + 1 } =
        false ∧
      fullShapeB { proofSizedFull.batch.shape with
        fold := { proofSizedFull.batch.shape.fold with
          index := { proofSizedFull.batch.shape.fold.index with
            v := proofSizedFull.batch.shape.fold.index.v + 1 } } } = false := by decide +kernel

/-- **At the closed letters of the head's law.** -/
theorem fullShape_at_name {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl} (hZ : VerifierAndGoals.InScope Z = true)
    (_ : VerifierAndGoals.readFiles Z = .ok pp) (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    fullShapeB (At.P13 Zp).lin = true := by
  show fullShapeB Zp.first.lin = true
  rw [(first_written_in_scope hZ L.pub hy).2.1]
  exact fullShape_written

end P5J

#print axioms P5J.fullShape_written
#print axioms P5J.fullShape_rejects
#print axioms P5J.fullShape_at_name
