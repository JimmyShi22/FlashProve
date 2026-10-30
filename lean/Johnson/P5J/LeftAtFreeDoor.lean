-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/LeftAtFreeDoor.lean: THE MEMBER `h.ThreeLeft h.free` WITH TWO OF ITS THREE PREMISES
BROUGHT FURTHER DOWN. One structure, five theorems.

`left_at_free` (Johnson/P5J/LeftAtFree.lean) leaves three premises: head_cuts, hw (the window) and
S. head_cuts enters here as the field itself; by report
`head_cuts_at_head` (Johnson/Desc/Kinds/Law/HeadCutsAtHead.lean) pays it. The other two:

  `window_at_free`: hw from hT : `Desc.K14.Law.Sh.Tests h.toAtMg.shPlan` (the shared table's tests
    on the plan), by `window_at_const` (Johnson/P5J/OmegaWindowAtConst.lean) at the value's letters.
  `three_at_free_of_tests`: h.Three h.free from head_cuts, hT and S.
  `AtMgA.DoorPrem h V`: what `Desc.K14.Law.ShDoor.SH₃_at_free`
    (Johnson/Desc/Last/ShapeDoorAtFree.lean) still asks, at own seats V: hi, hw, h6, h7 (four
    equations on V; MIND: `DoorPrem.hw` is that theorem's own binder's name and is not the window
    hw) and hR (inside the first table's last promise, under the head's condition,
    without a failure mark: `FourFacts V`).
  `left_at_free_door`: h.ThreeLeft h.free from head_cuts, hT and ∃ V, h.DoorPrem V. SH₃ is paid by
    `SH₃_at_free`; its hZ by the head, its hlen by `shared_row_twelve`
    (Johnson/P5J/SharedRowTwelve.lean).
  `three_at_free_door`: and so h.Three h.free.
  **`three_at_free_named`**: h.Three h.free, hR paid by `hR_at_head`
    (Johnson/Desc/Last/FourAtRc.lean).
    WHAT STAYS, BY NAME:
      head_cuts: the field itself.
      closed conditions: hT (on Zp, Np) · hi · hwV · h6 · h7 (on the own seats V) · hsp (on Zp) ·
        T (`PlanSits`) · hNum. T and hNum are closed once L, M and nW are laid (meant: the laid
        places and the messages' shapes of the planner's first chain; nW by hNum).
      one fact on reached states: hTwo (at every typed public part, at every state that the first
        chain reaches at border 357 without a failure mark: the seats are carried and the
        messages' shapes stand).
    V IS A LETTER ON PURPOSE. The meant V is `LLT25.vAt Zp (At.N Zp cF)`, where hi and hwV are rfl.
    This file does not import that constant's file.

Read against Johnson/P5J/FreeAll.lean, Johnson/Desc/K14/Law/SharedConstAtFree.lean,
Johnson/P5J/OmegaWindowAtConst.lean, Johnson/P5J/SharedRowTwelve.lean,
Johnson/Desc/Last/FourAtRc.lean and Johnson/Desc/Last/ShapeDoorAtFree.lean.
DoorPrem's five fields are `SH₃_at_free`'s own binders in that file,
compared by program.
Limits. A joining: it pays no field by itself. That the premises can be met is not shown here; that
one V meets DoorPrem's five together is shown by nobody. V is all but fixed by hi, DoorPrem.hw and
hR: the candidate is `LLT25.vAt Zp (At.N Zp cF)`; `PlanSits` has been evaluated there, at one set of
full-size files.
At the second hash function `OnBytes.secondHashFunction` alone. No soundness follows from it. Nothing on hiding.

-/
import Johnson.P5J.LeftAtFree
import Johnson.P5J.OmegaWindowAtConst
import Johnson.P5J.SharedRowTwelve
import Johnson.Desc.Last.ShapeDoorAtFree
import Johnson.Desc.Last.FourAtRc

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Iop.Reduction (steps)
open _root_.Run _root_.Run.PQ

open VerifierAndGoals.AtTheName
open VerifiableInference.Desc (Chain KindName)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

set_option quotPrecheck false in
/-- The shared table's constant's numbers, at the head. -/
local notation "NS" => Desc.K14.Law.Sh.nums h.toAtMg.shPlan (h.toAtMg.shOpen h.𝔇)

set_option quotPrecheck false in
/-- The three rows of pieces, at the value's letters. -/
local notation "TF" => (h.toAtMg.threeOf h.free.e₁ h.free.e₂ h.free.e₃ h.free.dW h.free.wEnd)

/-- **The window at the value**, from the shared table's tests on the plan. -/
theorem window_at_free (hT : Desc.K14.Law.Sh.Tests h.toAtMg.shPlan) :
    (NS).lo ≤ ((NS).tenant .oOmega).1 ∧
      ((NS).tenant .oOmega).1 < hiAt (1 + (TF).l₂.length) (TF).p₂ (TF).l₂ := by
  exact window_at_const OnBytes.secondHashFunction Zp Np cF (D.at frS.P.T.a) h.laid.planOk
    (by rw [LaidAt.atDepth h.scope h.laid]; exact h.laid.data)
    h.free.c₁ h.free.k₁ h.free.c₂ h.free.k₂ h.free.c₃ h.free.k₃ h.free_q₁ h.free_q₂ h.free_q₃
    (restCap h.free.e₁) (restCap h.free.e₂) (restCap h.free.e₃) h.free.dW h.free.wEnd hT
    (At.N Zp cF)

/-- **`h.Three h.free`** from head_cuts, the tests on the plan, and SH₃'s five. -/
theorem three_at_free_of_tests
    (head_cuts : fieldAt fun V : h.ThreeLeft h.free => ThreeLeftF.head_cuts V)
    (hT : Desc.K14.Law.Sh.Tests h.toAtMg.shPlan)
    (S : h.toAtMg.Sh3Owed h.𝔇 h.free) : h.Three h.free :=
  three_at_free_of h head_cuts (window_at_free h hT) S

/-- **What `SH₃_at_free` still asks**, at own seats V. -/
structure AtMgA.DoorPrem (V : OwnSeats) : Prop where
  /-- V's index seat is the first table's -/
  hi : V.index = (At.N Zp cF).index
  /-- V's seat of the message W is the first table's -/
  hw : V.w = (At.N Zp cF).w
  /-- the index message has one out-of-domain answer -/
  h6 : V.indexShape.answers = 1
  /-- the message W has one out-of-domain answer -/
  h7 : V.wShape.answers = 1
  /-- inside the first table's last promise, under the head's condition, without a failure mark -/
  hR : ∀ (q : ProofFile.InstPub × TS) (y : Strs),
    ocEnd (fun a : ProofFile.InstPub × TS => (a.1, a.2)) (At.N Zp cF) (h.toAtMg.mq h.𝔇) fullLinks At.ps
      q y →
    h.toAtMg.rc q → q.2.failed = none → FourFacts V q.2

/-- **The member, SH₃ by `SH₃_at_free`.** -/
theorem left_at_free_door
    (head_cuts : fieldAt fun V : h.ThreeLeft h.free => ThreeLeftF.head_cuts V)
    (hT : Desc.K14.Law.Sh.Tests h.toAtMg.shPlan)
    (S : ∃ V, h.DoorPrem V) : h.ThreeLeft h.free := by
  obtain ⟨V, S⟩ := S
  exact ThreeLeftF.mk head_cuts
    ⟨by exact Desc.K14.Law.Sh.TP_at_free h 0 h.free.ML h.free.PLm h.free.e₁ h.free.e₂ h.free.e₃
            h.free.dW h.free.wEnd,
     by exact Desc.K14.Law.Sh.PW_at_free h 0 h.free.ML h.free.PLm h.free.e₁ h.free.e₂ h.free.e₃
            h.free.dW h.free.wEnd,
     by exact Desc.K14.Law.ShDoor.SH₃_at_free h 0 h.free.ML h.free.e₁ h.free.e₂ h.free.e₃
            h.free.dW h.free.wEnd h.laid.pub V S.hi S.hw S.h6 S.h7 S.hR
            (shared_row_twelve h.scope h.laid
              (h.toAtMg.ofDesc h.free h.free_q₁ h.free_q₂ h.free_q₃)),
     by exact Desc.K14.Law.Sh.POf_at_free h 0 h.free.ML h.free.PLm h.free.e₁ h.free.e₂ h.free.e₃
            h.free.dW h.free.wEnd (window_at_free h hT),
     by exact Desc.K14.Law.Sh.POb_at_free h 0 h.free.ML h.free.PLm h.free.e₁ h.free.e₂ h.free.e₃
            h.free.dW h.free.wEnd (window_at_free h hT),
     h.toAtMg.stepQ_field h.𝔇 h.free _ (by exact rfl)⟩

/-- **`h.Three h.free`** from head_cuts, the tests on the plan, and what `SH₃_at_free` asks. -/
theorem three_at_free_door
    (head_cuts : fieldAt fun V : h.ThreeLeft h.free => ThreeLeftF.head_cuts V)
    (hT : Desc.K14.Law.Sh.Tests h.toAtMg.shPlan)
    (S : ∃ V, h.DoorPrem V) : h.Three h.free :=
  three_at_free h (left_at_free_door h head_cuts hT S)

section Named
open ToldDesc (PlanSits)
open VerifiableInference.Desc.K12.Door (Laid seatsCarriedB msgShapesB)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- **`h.Three h.free` from head_cuts, closed conditions and one fact on reached states.** -/
theorem three_at_free_named
    (head_cuts : fieldAt fun V : h.ThreeLeft h.free => ThreeLeftF.head_cuts V)
    (hT : Desc.K14.Law.Sh.Tests h.toAtMg.shPlan)
    {V : OwnSeats} (hi : V.index = (At.N Zp cF).index) (hwV : V.w = (At.N Zp cF).w)
    (h6 : V.indexShape.answers = 1) (h7 : V.wShape.answers = 1)
    {L : Laid} {M : List OracleShape} {nW : ℕ}
    (hTwo : ∀ z s₂, h.toAtMg.typed z →
      Reach 0 (cF.blocksInOrder.map VerifiableInference.Desc.Sound.below) (ProofFile.startS Zp) 357 (z, s₂) →
      s₂.failed = none → seatsCarriedB L s₂.book = true ∧ msgShapesB M s₂.st = true)
    (hsp : (VerifiableInference.Desc.K13.whereOf Zp).lin.ownSplitNeeded = false)
    (T : PlanSits L M V (At.N Zp cF).indexNo nW)
    (hNum : (At.N Zp cF).msgsAt none = nW + wMsgs Zp) : h.Three h.free :=
  three_at_free_door h head_cuts hT
    ⟨V, ⟨hi, hwV, h6, h7, hR_at_head h.toAtMg h.𝔇 hTwo hsp T hNum⟩⟩

end Named

end P5J

#print axioms P5J.window_at_free
#print axioms P5J.three_at_free_of_tests
#print axioms P5J.left_at_free_door
#print axioms P5J.three_at_free_door
#print axioms P5J.three_at_free_named
