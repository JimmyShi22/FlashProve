-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/OneOmegaAtHead.lean: THE SEVENTH OF THE NAMED TESTS ON SEATS OF THE LAST TABLE's
PREMISE hP (LLT25.PlanOk₃'s field oneOmega) SAYS TRUE UNDER THE ONE HEAD P5J.AtMg: the
test with code ToldDesc.oneOmegaB (Johnson/ToldDescR/OneOmegaB.lean) at the own test's place and
nΩ := 1. Statements and proofs.

  oneOmega_written    a closed fact, by the kernel: at K12's files' closed place piWFull every
                      opening under "taken 1 n" has n = 1
  oneOmega_can_fail   the closed fact can fail: at nΩ := 0 it is false
  rounds_at_head      under the head the own test's block declares the closed place's rounds
  **oneOmega_at_head**

CALLED, ALL K12's FILES': rounds_at_seat_W (Johnson/Loose/H2K12/RoundsAtFull.lean): the made
place's numbers give the closed place's rounds; rdsAt_reads
(Johnson/Desc/K12/Law/Sizes/ClosedAtScope.lean): so the two blocks declare the same rounds;
plan_at_seat_W, atFull_of_pubPlain, nums_of_planOk, closed_WFull. And seat_in_scope
(Johnson/Goal/Numbers/PlanWrittenDescScope.lean) at LPFD.asks_written: the entry tests' FIRST row:
the thirteen-row list is not needed.
At every function o in the second hash function's place. What is not claimed. That a head can be had
at any public files. The full size alone. No member. No soundness.

-/
import Johnson.ToldDescR.OneOmegaB
import Johnson.Loose.H2K12.RoundsAtFull
import Johnson.Loose.H2K12.ClosedAtSeats
import Johnson.Loose.H2K12.AtFullPlain
import Johnson.Desc.K12.Law.Sizes.ClosedAtScope
import Johnson.Goal.Numbers.PlanWrittenDescScope
import Johnson.Desc.Laid.ProofAsksLaw
import Johnson.P5J.AtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM.Seats

open VerifiableInference.Desc VerifiableInference.Desc.K12
open OnBytes.Maker (WholeD)
open H2K.Member (piWFull)
open ToldDesc (oneOmegaB)
open P5J

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

set_option maxRecDepth 1000000 in
/-- At the closed place: every opening under "taken 1 n" has n = 1. -/
theorem oneOmega_written : oneOmegaB piWFull 1 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The closed fact can fail. -/
theorem oneOmega_can_fail : oneOmegaB piWFull 0 = false := by decide +kernel

/-- Under the head the own test's block declares the closed place's rounds. -/
theorem rounds_at_head (h : AtMg o Z D r Zp Np cF) :
    (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W) : Block T12 Unit).rounds =
      (proximityTestKind guardedProximityTestParts piWFull : Block T12 Unit).rounds := by
  have hpN : (H2K.JointK.descN o ProofFile.pureRoad.links guardedProximityTestParts Zp Np cF).planOk = true :=
    h.laid.planOk
  have hpW := H2K.JointK.plan_at_seat_W o Zp ProofFile.pureRoad.links Np cF hpN
  have hW := (VerifiableInference.PlanWritten.seat_in_scope _ _ Z h.scope
    (LPFD.asks_written h.laid.asks)).1
  have hR := H2K.JointK.rounds_at_seat_W o Zp ProofFile.pureRoad.links Np cF h.laid.places hpN
    (H2K.Sizes.atFull_of_pubPlain h.scope h.laid.pub) hW
  have hn := H2K.Made.nums_of_planOk ⟨3, none, 2, .K12⟩ Np.W hpW
  exact H2K.Sizes.rdsAt_reads hpW VerifiableInference.Desc.K12.Coin.At.closed_WFull.plan
    (by rw [hn]; exact hR)

/-- **oneOmega.** -/
theorem oneOmega_at_head (h : AtMg o Z D r Zp Np cF) :
    oneOmegaB (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W) 1 = true := by
  have e : oneOmegaB (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W) 1 = oneOmegaB piWFull 1 := by
    unfold oneOmegaB
    rw [rounds_at_head h]
  rw [e]
  exact oneOmega_written

end IM.Seats

#print axioms IM.Seats.oneOmega_written
#print axioms IM.Seats.oneOmega_can_fail
#print axioms IM.Seats.rounds_at_head
#print axioms IM.Seats.oneOmega_at_head
