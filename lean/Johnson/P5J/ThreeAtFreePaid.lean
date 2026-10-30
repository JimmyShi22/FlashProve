-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/ThreeAtFreePaid.lean: `h.Three h.free` WITH hT AND SH₃'s FIVE PAID BY NAME. One theorem.

`three_at_free_door` (Johnson/P5J/LeftAtFreeDoor.lean) gives h.Three h.free from head_cuts, hT (the
shared table's tests on the plan) and ∃ V, h.DoorPrem V (hi, hw, h6, h7, hR).
Here hT and all five of DoorPrem are paid by name, with the own seats V laid at
`LLT25.vAt Zp (At.N Zp cF)`:

  hT: `Desc.K14.Law.Sh.tests_at_head` (Johnson/Desc/K14/Law/SharedConstChainOkAtHead.lean); from the
    head and the pin hy.
  hi · hw: `vAt_index` | `vAt_w` (Johnson/Desc/Last/DoorAtV.lean); rfl.
  h6 · h7: `Second.Seam.answers_one_in_scope` (Johnson/Second/Seam/AnswersOneInScope.lean); from the
    head and the same pin hy.
  hR: `hR_at_head_end` (Johnson/Desc/Last/FourAtRcEnd.lean); from hEnd, T and hNum.

  **`three_at_free_paid`**: h.Three h.free. WHAT STAYS, BY NAME AND CLASS:
    head_cuts: a field of the join, as itself. It is paid, with hy, from one row of tests in
      Johnson/P5J/ThreeAtFreeRow.lean.
    hy: ONE PIN: a closed test on the public part (`madePinnedAt` accepts). It is spent three times
      (hT, h6, h7). Who pays it: where the laws ask thirteen rows or more (by the file's rule
      that tests are only appended: Johnson/Desc/Laid/ProofAsks.lean; this library's list has
      fourteen), the head (`LPFD.asks_pins` with
      `pinnedAt_of_row`), by reading; where they ask eight, nobody.
    T (`PlanSits`) · hNum: closed once L, M and nW are laid (meant: the laid places and the
      messages' shapes of the planner's first chain; nW by hNum).
    hEnd: the one fact on reached states, asked at the first chain's last border (358) alone: at
      every typed public part, at every state reached there without a failure mark, the seats are
      carried and the messages' shapes stand. Its payer: `IM.hEnd_paid`; from the head:
      `hEnd_at_head_under`; Johnson/P5J/ThreeAtFreeNoStates.lean calls it.

It stands in the ported world: DoorAtV imports Johnson.LLT25R.LastAt.
Read against Johnson/P5J/LeftAtFreeDoor.lean, Johnson/Desc/K14/Law/SharedConstChainOkAtHead.lean,
Johnson/Desc/Last/DoorAtV.lean, Johnson/Desc/Last/FourAtRcEnd.lean and
Johnson/Second/Seam/AnswersOneInScope.lean, which may still turn.
Limits. A joining: it pays nothing by itself. That what stays can be met is not shown here.
At the second hash function `OnBytes.secondHashFunction` alone. No soundness follows from it. Nothing on hiding.

-/
import Johnson.P5J.LeftAtFreeDoor
import Johnson.Desc.K14.Law.SharedConstChainOkAtHead
import Johnson.Desc.Last.DoorAtV
import Johnson.Desc.Last.FourAtRcEnd
import Johnson.Second.Seam.AnswersOneInScope

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

open ToldDesc (PlanSits)
open VerifiableInference.Desc.K12.Door (Laid seatsCarriedB msgShapesB)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- **`h.Three h.free` from head_cuts, one pin, two closed conditions and one fact on reached
states.** -/
theorem three_at_free_paid
    (head_cuts : fieldAt fun V : h.ThreeLeft h.free => ThreeLeftF.head_cuts V)
    (hy : VerifiableInference.PlanWritten.madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made =
      true)
    {L : Laid} {M : List OracleShape} {nW : ℕ}
    (hEnd : ∀ z s, h.toAtMg.typed z →
      Reach 0 (cF.blocksInOrder.map VerifiableInference.Desc.Sound.below) (ProofFile.startS Zp) 358 (z, s) →
      s.failed = none → seatsCarriedB L s.book = true ∧ msgShapesB M s.st = true)
    (T : PlanSits L M (LLT25.vAt Zp (At.N Zp cF)) (At.N Zp cF).indexNo nW)
    (hNum : (At.N Zp cF).msgsAt none = nW + wMsgs Zp) : h.Three h.free :=
  three_at_free_door h head_cuts
    (by exact Desc.K14.Law.Sh.tests_at_head h hy _)
    ⟨LLT25.vAt Zp (At.N Zp cF),
      ⟨vAt_index _ _, vAt_w _ _,
        by exact (Second.Seam.answers_one_in_scope h.scope h.laid.pub hy).1,
        by exact (Second.Seam.answers_one_in_scope h.scope h.laid.pub hy).2,
        hR_at_head_end h.toAtMg h.𝔇 hEnd T hNum⟩⟩

end P5J

#print axioms P5J.three_at_free_paid
