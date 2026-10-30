-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/SendFitAtHead.lean: the public check on the shapes of the shared
chain's two sendings, `sendingsFit` (Johnson/Desc/ProofFile/Honest/K14/SendingsShapes.lean), is true
at the proof file's own plan `qAt Zp Np` (Johnson/Desc/K1/Law/SitsShared.lean), under the library's
head (`P5J.AtMg`, Johnson/P5J/AtMg.lean). It imports Mathlib.

  `sendingsFit_plan`   of a plan the check reads the codes and the shape alone
  `send_real`     the check at the typed sizes (`realSized`, Johnson/Desc/K1/Law/CondReal.lean),
                 evaluated by Lean's kernel
  `sendingsFit_head`   the check at `qAt Zp Np`, under the head

By what. As in FitAtHead.lean: `written_at_head` and `qAt_written` give the plan's codes and shape
under the head; then one evaluation. Johnson/Desc/ProofFile/Honest/K14/SendingsAtHead.lean shows the
like under a premise that asks more (`P5J.AtMgA`, which extends `P5J.AtMg`), at a definition with
the same short name; it is not imported here.

Limits. The full size alone. `sendingsFit` is defined in
Johnson/Desc/ProofFile/Honest/K14/SendingsShapes.lean, a file of another folder; what it does not
ask is said in that file's head. No definition of this folder evaluates it. No example of the head
is shown here. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.FitAtHead
import Johnson.Desc.ProofFile.Honest.K14.SendingsShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc.K1 (qAt realSized)
open Johnson.G (codesFull2)
open Desc.K14 (P14)
open ProofFile.Honest.K14 (sendingsFit)

theorem sendingsFit_plan (Q : P14) : sendingsFit Q = sendingsFit (planOf Q.codes Q.S).P := rfl

theorem send_real : (realSized.all fun q => sendingsFit (planOf q.2 q.1.shape).P) = true := by
  decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **The check on the two sendings' shapes at the shared chain's own plan, under the head.** -/
theorem sendingsFit_head (h : P5J.AtMg o Z D r Zp Np cF) : sendingsFit (qAt Zp Np) = true := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  have eC : (qAt Zp Np).codes = codesFull2 := by rw [qAt_written Wr Np]
  have eS : (qAt Zp Np).S = x.shape := by rw [qAt_written Wr Np]
  have k := send_real
  rw [hx] at k
  rw [sendingsFit_plan, eC, eS]
  exact k

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.sendingsFit_plan
#print axioms ProofFile.Honest.K12.Light.send_real
#print axioms ProofFile.Honest.K12.Light.sendingsFit_head
