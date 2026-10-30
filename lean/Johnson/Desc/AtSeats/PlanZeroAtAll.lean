-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/PlanZeroAtAll.lean: THE FIELD planG OF WHAT IS STILL OWED FOR KIND K1's
CONDITION (`K1Owed`, Johnson/Desc/AtSeats/K01CondOfRest.lean), AT THE FIRST TABLE's CLOSED
CONSTANT's HEAD, IN THE FIELD's OWN TYPE: the closed test `planZeroB` accepts at the public part's
own list of segments and public parameters. One statement with its proof: a call of
`planZero_in_scope` (Johnson/Desc/AtSeats/PlanZeroInScope.lean) at the head's scope and at
`hOk_atAll` (Johnson/Desc/K1/Law/TestsAtAll.lean). PREMISES: the head hA and the opening O.
A PAYMENT BENEATH A FROZEN CONDITION: no statement above turns. What is not claimed. That the head
or the opening can be met. Nothing on soundness. Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.AtSeats.PlanZeroInScope
import Johnson.Desc.K1.Law.TestsAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile (Cl)
open IM (Open)

/-- **The field planG.** -/
theorem planG_atAll {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase}
    {base₀ : List (Block S Cl)} (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
    (O : Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    K13.Law.planZeroB Zp.p.built.links Zp.p.X false = true :=
  K13.Law.planZero_in_scope hA.scope hA.reads O fun b hb => (hOk_atAll hA O b hb).1

end VerifiableInference.Desc.K1
