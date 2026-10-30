-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/CoreOfTwoRadii.lean: WHAT STAYS OF THE TESTS ON THE LAST TABLE's PLAN, AT THE JOIN's
OWN LETTERS (`P5J.L0.CoreJ`, Johnson/P5J/L0/PlanAtHead.lean), FROM THE HEAD AND TWO TESTS ON RADII.
One theorem. A joining: no test and no law is typed here.

  `core_of_two_radii`: (h : `AtMgA OnBytes.secondHashFunction Z D r' Zp Np cF x`) (hRW) (hRI) ⊢ for every dB, dt
    that the third piece's stretch of the written rounds is: `CoreJ` at `L0.sevenJ` and
    `L0.ldAt Zp`: the very premise C of `L0.planOk₃_at_join` (Johnson/P5J/L0/PlanAtJoin.lean).
    hRW | hRI: at the first stage of the last block's test, `radB` (Johnson/P2LawR/PlanLeftAt.lean)
      accepts at whoever of the first table's members sits at W's seat | at the index's seat.
  ALL FIFTEEN FIELDS ARE CALLS: the fourteen of `core_of_planAt` (Johnson/P2LawR/CoreOfPlanAt.lean,
    which names them), with its pin met by `P5J.AtMg.made_accepts`, and:
    planAt: `P5J.AtMg.planAt_two_radii` (Johnson/P2LawR/PlanAtTwoRadii.lean): the field's own text.
      Its premises beside hRW | hRI: the equations on the public value and the shared table's named
      tests: `Sh.written_of_made` | `Sh.tests_at_head` (Johnson/Desc/K14/Law/SharedConstCodesMade |
      SharedConstChainOkAtHead.lean) · the description's test on its plan: the head's field · its
      data at the frame's depth: `P5J.AtMg.dataL` (Johnson/P5J/L0/PlanAtHead.lean) · the fields
      seats · oneSeat · mineW · mineI: as above.

Limits. hRW and hRI are premises: NOTHING IS EVALUATED HERE. A member of the head is proved at
`storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). At `OnBytes.secondHashFunction` alone. The
full size alone. Nothing is said on what a radius means: numbers are compared. Nothing on soundness.

One limit is raised: maxRecDepth to 40000.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P2LawR.CoreOfPlanAtHead
import Johnson.P2LawR.PlanAtTwoRadii
import Johnson.Desc.K14.Law.SharedConstChainOkAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P2Law.Left
open P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker OnBytes.Flat
open OnBytes.Road OnBytes.RunA
open Iop Prob _root_.Run _root_.Run.PQ
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (ModelPart Item Numbers)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law
open ToldDesc (p14At)
open LLT25

open LLT25.PlanB
open P2Law.PlanLeft

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r' : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The premise C of `planOk₃_at_join`, from the head and two tests on radii.** -/
theorem core_of_two_radii (h : AtMgA OnBytes.secondHashFunction Z D r' Zp Np cF x)
    (hRW : ∀ st rest, (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W).nums.stages = st :: rest →
      (((At.ms Zp Z.lay).filter fun y => decide (y.1.seat y.2 = (At.N Zp cF).w)).all
        fun y => radB (p14At Zp).codes H2K.Member.rWFull st y) = true)
    (hRI : ∀ st rest, (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W).nums.stages = st :: rest →
      (((At.ms Zp Z.lay).filter fun y => decide (y.1.seat y.2 = (At.N Zp cF).index)).all
        fun y => radB (p14At Zp).codes H2K.Member.rWFull st y) = true) :
    ∀ dB dt, L0.StretchJ OnBytes.secondHashFunction D Zp Np cF dB dt →
      L0.CoreJ OnBytes.secondHashFunction Z D Zp Np cF (L0.sevenJ OnBytes.secondHashFunction Zp Np cF) dB dt
        (L0.ldAt Zp) := by
  have hy := h.toAtMg.made_accepts
  obtain ⟨x₀, hx, hw⟩ := _root_.Desc.K14.Law.Sh.written_of_made h.scope h.laid.pub hy
    (_root_.Desc.K14.Law.Sh.laidPOf_at_head h)
  intro dB dt s
  exact
  { nodup := L0.nodup_at_join h.toAtMg
    seats := L0.seats_at_join h.toAtMg hy _
    fence := L0.fence_at_join h.toAtMg
    placeB := L0.placeB_at_head h.toAtMg dB dt s
    someW := some_of (IM.Seats.someW_at_head h.toAtMg)
    someI := some_of (IM.Seats.someI_at_head h.toAtMg)
    oneSeat := oneSeat_of (IM.Seats.oneSeat_at_join h.toAtMg)
    oneOmega := (ToldDesc.oneOmega_iff _ _).1 (IM.Seats.oneOmega_at_head h.toAtMg)
    omegaSeat := omegaSeat_of (IM.Seats.omegaSeat_at_join h.toAtMg)
    mineI := mineAt_of (IM.Seats.mineI_at_head h.toAtMg _ _)
    mineW := mineAt_of (IM.Seats.mineW_at_head h.toAtMg _ _)
    planAt := h.toAtMg.planAt_two_radii (F0T OnBytes.secondHashFunction Zp Np cF)
      (F0T OnBytes.secondHashFunction Zp Np cF) hx hw (_root_.Desc.K14.Law.Sh.tests_at_head h hy _)
      "proof file" (D.at frS.P.T.a) h.laid.planOk h.toAtMg.dataL
      (D.at frS.P.T.a).key₃ (FL OnBytes.secondHashFunction ProofFile.pureRoad.links Zp (seatK Zp Np) Np cF).lastChainFirstTreeNumber
      (At.ms Zp Z.lay) (At.N Zp cF) (0, 0) (0, 0) (L0.seats_at_join h.toAtMg hy _)
      (oneSeat_of (IM.Seats.oneSeat_at_join h.toAtMg))
      (mineAt_of (IM.Seats.mineW_at_head h.toAtMg _ _))
      (mineAt_of (IM.Seats.mineI_at_head h.toAtMg _ _)) hRW hRI
    oneTable := L0.oneTable_at_join h.toAtMg
    planShapes := by rw [ldAt_is_full h.toAtMg hy]; exact L0.planShapes_at_head h.toAtMg
    indexNeW := L0.indexNeW_at_head h.toAtMg }

end P2Law.Left

#print axioms P2Law.Left.core_of_two_radii
