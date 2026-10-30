-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P2LawR/CoreOfPlanAt.lean: WHAT STAYS OF THE TESTS ON THE LAST TABLE's PLAN, AT THE JOIN's
OWN LETTERS (`P5J.L0.CoreJ`, Johnson/P5J/L0/PlanAtHead.lean), FROM THE HEAD, ONE PIN AND ONE TEST
WITH CODE. One theorem. A joining: no test and no law is typed here.

  `core_of_planAt`: (h : `AtMgA OnBytes.secondHashFunction Z D r' Zp Np cF x`) (hy) (tP) ⊢ for every dB, dt that
    the third piece's stretch of the written rounds is: `CoreJ` at `L0.sevenJ` and `L0.ldAt Zp`: the
    very premise C of `L0.planOk₃_at_join` (Johnson/P5J/L0/PlanAtJoin.lean).
    hy : `madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true`: a test with code on
      written values of the plan: spent by the field seats and to lay the written list at
      `L0.ldAt Zp`.
    tP : `planAtAllB … = true` at the join's letters: at the first stage each member's plan fits:
      what `LLT25.PlanAt` asks beyond the field seats.
  FOURTEEN OF THE FIFTEEN FIELDS ARE CALLS FROM THE HEAD: the twelve of `coreJ_at_head`
    (Johnson/P2LawR/CoreJAtHead.lean, which names each), and:
    seats: `P5J.L0.seats_at_join` (Johnson/P5J/L0/SeatsAtJoin.lean): the field's own text, under hy.
    oneOmega: `IM.Seats.oneOmega_at_head` (Johnson/IMR/OneOmegaAtHead.lean): the test accepts; its
      law.
  planAt: by its test's law (`planAtAll_law`, Johnson/P2LawR/PlanLeftAt.lean) from tP and seats.
  OVERTAKEN: `core_of_two_radii` (Johnson/P2LawR/CoreOfTwoRadii.lean), its two tests on radii met by
  `P5J.AtMg.two_radii` (Johnson/P2LawR/TwoRadiiAtHead.lean), has the same end from the head alone:
  so it is called in Johnson/P2LawR/LastLeftAlone.lean.

Limits. hy and tP are premises: NOTHING IS EVALUATED HERE. A member of the head is proved at `storedPublicFiles`
and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). At `OnBytes.secondHashFunction`
alone. The full size alone. Nothing on soundness.

One limit is raised: maxRecDepth to 40000.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P2LawR.CoreJAtHead
import Johnson.P5J.L0.SeatsAtJoin
import Johnson.IMR.OneOmegaAtHead

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
open VerifiableInference.PlanWritten (madePinnedAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r' : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The premise C of `planOk₃_at_join`, from the head, one pin and one test with code.** -/
theorem core_of_planAt (h : AtMgA OnBytes.secondHashFunction Z D r' Zp Np cF x)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
    (tP : planAtAllB (F0T OnBytes.secondHashFunction Zp Np cF) (p14At Zp).codes (frJ D Zp Np cF)
      H2K.Member.rWFull (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W).nums.stages (mineJ Z Zp Np cF) = true) :
    ∀ dB dt, L0.StretchJ OnBytes.secondHashFunction D Zp Np cF dB dt →
      L0.CoreJ OnBytes.secondHashFunction Z D Zp Np cF (L0.sevenJ OnBytes.secondHashFunction Zp Np cF) dB dt (L0.ldAt Zp) :=
  fun dB dt s =>
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
    planAt := planAtAll_law _ _ _ _ _ _ (L0.seats_at_join h.toAtMg hy _) tP
    oneTable := L0.oneTable_at_join h.toAtMg
    planShapes := by rw [ldAt_is_full h.toAtMg hy]; exact L0.planShapes_at_head h.toAtMg
    indexNeW := L0.indexNeW_at_head h.toAtMg }

end P2Law.Left

#print axioms P2Law.Left.core_of_planAt
