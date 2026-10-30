-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P2LawR/CoreJAtHead.lean: WHAT STAYS OF THE TESTS ON THE LAST TABLE's PLAN, AT THE JOIN's
OWN LETTERS (`P5J.L0.CoreJ`, Johnson/P5J/L0/PlanAtHead.lean: `LLT25.PlanCore₃`: fourteen fields and
indexNeW), FROM THE HEAD AND WHAT IS STILL A TEST BY NAME. Two abbreviations, one structure, one
theorem. A joining: no test and no law is typed here.

  `CoreRest h`: one field for each of the fifteen that is a test with code by name here: 3
    (seats · oneOmega · planAt); and the field pin.
  `coreJ_at_head`: (h : `AtMgA OnBytes.secondHashFunction Z D r' Zp Np cF x`) (R : `CoreRest h`) ⊢ for every
    dB, dt that the third piece's stretch of the written rounds is: `CoreJ` at `L0.sevenJ` and
    `L0.ldAt Zp`: the very premise C of `L0.planOk₃_at_join` (Johnson/P5J/L0/PlanAtJoin.lean).
  CALLED, 12 of fifteen:
    placeB: `P5J.L0.placeB_at_head` (Johnson/P5J/L0/PlaceBAtHead.lean): the field's own text, from
      the head and the stretch.
    nodup: `P5J.L0.nodup_at_join` (Johnson/P5J/L0/PlanFourAtJoin.lean): the field's own text.
    fence: `P5J.L0.fence_at_join` (the same file): the field's own text.
    oneTable: `P5J.L0.oneTable_at_join` (the same file): the field's own text.
    planShapes: `P5J.L0.planShapes_at_head` (the same file): the field's text at the written list
      `LFull`, laid at `L0.ldAt Zp` by `ldAt_is_full` (Johnson/P2LawR/LdAtLeft.lean) under the field
      pin.
    indexNeW: `P5J.L0.indexNeW_at_head` (the same file): the field's own text.
    someW: `IM.Seats.someW_at_head` (Johnson/IMR/SeatsAtHead.lean): the test accepts; its law.
    someI: `IM.Seats.someI_at_head`: the test accepts; its law.
    oneSeat: `IM.Seats.oneSeat_at_join`: the test accepts; its law.
    omegaSeat: `IM.Seats.omegaSeat_at_join`: the test accepts; its law.
    mineI: `IM.Seats.mineI_at_head`: the test accepts; its law.
    mineW: `IM.Seats.mineW_at_head`: the test accepts; its law.
  BY ITS TEST's LAW (Johnson/P2LawR/PlanCoreOfTests.lean names each law's file): the others.

Limits. NO TEST IS EVALUATED HERE: a field of `CoreRest` is a premise. A member of the head is
proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/). At
`OnBytes.secondHashFunction` alone. The full size alone. Nothing on soundness.

One limit is raised: maxRecDepth to 40000.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P5J.L0.PlanAtJoin
import Johnson.P5J.L0.LastLeftAt
import Johnson.P2LawR.PlanCoreOfTests
import Johnson.P5J.L0.PlaceBAtHead
import Johnson.P5J.L0.PlanFourAtJoin
import Johnson.P2LawR.LdAtLeft
import Johnson.IMR.SeatsAtHead

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

/-- The three members at the join's own letters. -/
abbrev mineJ (Z : VerifierAndGoals.PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) : List Mem :=
  mineOf (At.ms Zp Z.lay) (L0.ms2J (L0.sevenJ OnBytes.secondHashFunction Zp Np cF)) (At.N Zp cF)
    (L0.nsJ (L0.sevenJ OnBytes.secondHashFunction Zp Np cF))

/-- The last block's frame at the join's own letters. -/
abbrev frJ (D : WholeD) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) :=
  frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₃
    (FL OnBytes.secondHashFunction ProofFile.pureRoad.links Zp (seatK Zp Np) Np cF).lastChainFirstTreeNumber

/-- **WHAT IS STILL A TEST BY NAME.** -/
structure CoreRest (_h : AtMgA OnBytes.secondHashFunction Z D r' Zp Np cF x) : Prop where
  /-- A test with code on written values of the plan: spent to lay the written list at `L0.ldAt Zp`.
  -/
  pin : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true
  /-- A test with code: each member's whole sending sits as the description tells. -/
  seats : P2Law.PlanLeft.seatsB (F0T OnBytes.secondHashFunction Zp Np cF) (p14At Zp).codes (mineJ Z Zp Np cF) =
    true
  /-- A test with code: the last block opens Omega's tree once. -/
  oneOmega : ToldDesc.oneOmegaB (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W) 1 = true
  /-- A test with code: at the first stage each member's plan fits, beyond the field seats. -/
  planAt : planAtAllB (F0T OnBytes.secondHashFunction Zp Np cF) (p14At Zp).codes (frJ D Zp Np cF)
    H2K.Member.rWFull (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W).nums.stages (mineJ Z Zp Np cF) = true

/-- **The premise C of `planOk₃_at_join`, from the head and what is still a test by name.** -/
theorem coreJ_at_head (h : AtMgA OnBytes.secondHashFunction Z D r' Zp Np cF x) (R : CoreRest h) :
    ∀ dB dt, L0.StretchJ OnBytes.secondHashFunction D Zp Np cF dB dt →
      L0.CoreJ OnBytes.secondHashFunction Z D Zp Np cF (L0.sevenJ OnBytes.secondHashFunction Zp Np cF) dB dt (L0.ldAt Zp) :=
  fun dB dt s =>
  { nodup := L0.nodup_at_join h.toAtMg
    seats := seatsB_law _ _ _ R.seats
    fence := L0.fence_at_join h.toAtMg
    placeB := L0.placeB_at_head h.toAtMg dB dt s
    someW := some_of (IM.Seats.someW_at_head h.toAtMg)
    someI := some_of (IM.Seats.someI_at_head h.toAtMg)
    oneSeat := oneSeat_of (IM.Seats.oneSeat_at_join h.toAtMg)
    oneOmega := (ToldDesc.oneOmega_iff _ _).1 R.oneOmega
    omegaSeat := omegaSeat_of (IM.Seats.omegaSeat_at_join h.toAtMg)
    mineI := mineAt_of (IM.Seats.mineI_at_head h.toAtMg _ _)
    mineW := mineAt_of (IM.Seats.mineW_at_head h.toAtMg _ _)
    planAt := planAtAll_law _ _ _ _ _ _ (seatsB_law _ _ _ R.seats) R.planAt
    oneTable := L0.oneTable_at_join h.toAtMg
    planShapes := by rw [ldAt_is_full h.toAtMg R.pin]; exact L0.planShapes_at_head h.toAtMg
    indexNeW := L0.indexNeW_at_head h.toAtMg }

end P2Law.Left

#print axioms P2Law.Left.coreJ_at_head
