-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/PlanGAtAll.lean: THE PREMISE G_hPlG OF KIND K1's SHARE
(`k01_kind_atThree` [not in this library],
Johnson/Desc/AtSeats/K01KindAtThree.lean [not in this library]) AT THE FIRST TABLE's CLOSED CONSTANT
(`P5J.AtMgA.𝔇`), IN THE BINDER's OWN TYPE. One statement with its proof: a call of `planG_at9`
(Johnson/Desc/AtSeats/PlanGOfTest.lean): the constant's list of segments is the list that `zeroAt`
reads, and its public parameters are the ones that it reads: both by rfl. ONE PREMISE IS LEFT: hB:
the closed test `planZeroB` accepts at the public part's own list and public parameters, at the
lookup argument on the calls. What is not claimed. hB. That the constant's head can be met.
Nothing on soundness. Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.AtSeats.PlanGOfTest
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law (PlanG planZeroB planG_at9)
open Johnson.Desc.First.Walk (LayPar)
open ProofFile (Cl)

theorem G_hPlG_atAll {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀) {G_X : LayPar}
    (hX : Johnson.Desc.First.Walk.Seat.zeroAt Zp.p.built.links Zp.p.X = some G_X)
    (hB : planZeroB Zp.p.built.links Zp.p.X false = true) :
    PlanG G_X hA.𝔇.pubD.nsOf hA.𝔇.pubD.d3 false hA.𝔇.shape hA.𝔇.layout :=
  planG_at9 hA.𝔇 rfl hX false hB

end VerifiableInference.Desc.K1
