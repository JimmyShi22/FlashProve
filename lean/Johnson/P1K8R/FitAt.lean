-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/FitAt.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: ONE PREMISE
OF THE KIND'S LAW AT THE CLOSED CONSTANT, PAID FROM THE HEAD ALONE. NO SOUNDNESS.

`k08_at_const` (ConstAt.lean) asks that every member of the plan's list fits the description
(`hFit`). `seatsFit_of_B`
(Johnson/Desc/Sound/PlanMemProofs.lean) gives it from the plain test `seatsFitB`, and the head's own
named test `PlanOk.fit` gives that test, as `PlanOk.hG` spends it
(Johnson/P5J/PlanOk.lean).
  `fit_at_const`: **under the head: every member of `P5J.At.ms Zp Z.lay` fits the description.**
Limits. That the head can be met is other files' to show. Nothing on soundness.

-/
import Johnson.P1K8R.ConstAt
import Johnson.Desc.Sound.PlanMemProofs

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open OnBytes OnBytes.Maker
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **The plan's members fit the description, from the head alone.** -/
theorem fit_at_const (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) :
    ∀ y ∈ P5J.At.ms Zp Z.lay,
      SeatFits (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) (P5J.At.cs Zp) y.1.l y.1.seat :=
  seatsFit_of_B (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (P5J.At.cs Zp) (P5J.At.members Zp Z.lay)
    ((P5T.seatsFitB_R _ _ _ _ _ (fun p hp _ => P5T.planSeats_send_lt Zp Zp.D.1 p hp)).trans
      h.plan.fit)

end P1K8T

#print axioms P1K8T.fit_at_const
