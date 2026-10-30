-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/ThreeAtFreeRow.lean: `h.Three h.free` FROM ONE ROW OF TESTS, TWO CLOSED CONDITIONS AND
ONE FACT ON REACHED STATES. One theorem.

`three_at_free_paid` (Johnson/P5J/ThreeAtFreePaid.lean) leaves head_cuts, the pin hy, T, hNum and
hEnd. One closed test pays the first two. It is hr: the row with `madeRow` behind its guard on the
key, as a verifier's list of tests writes it.

  head_cuts: `head_cuts_of_guard` (Johnson/Desc/Kinds/Law/HeadCutsFive.lean); from the head
    and hr. It ends in the field's own text; beside it stands a test of fit at `h.Three L`.
  hy: `VerifiableInference.PlanWritten.pinnedAt_of_row`
    (Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean); from hr.

  **`three_at_free_row`**: h.Three h.free. WHAT STAYS, BY NAME AND CLASS:
    hr: ONE ROW OF TESTS: closed, on the public part. It carries head_cuts, hT, h6 and h7. Under the
      head's scope the guard's left arm is false, so hr is `madeRow Zp = true` there. Who pays
      it: where the laws ask thirteen rows or more (by the file's rule that tests are only
      appended: Johnson/Desc/Laid/ProofAsks.lean; this library's list has fourteen), the head
      (`LPFD.asks_made_at`), by the file that
      declares it; where they ask eight, nobody.
    T (`PlanSits`) · hNum: closed once L, M and nW are laid (meant: the laid places and the
      messages' shapes of the planner's first chain; nW by hNum).
    hEnd: the one fact on reached states, at the first chain's last border (358) alone.

Read against Johnson/P5J/ThreeAtFreePaid.lean, Johnson/Desc/Kinds/Law/HeadCutsFive.lean and
Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean, which may still turn.
Limits. A joining: it pays nothing by itself. That what stays can be met is not shown here.
At the second hash function `OnBytes.secondHashFunction` alone. No soundness follows from it. Nothing on hiding.

-/
import Johnson.P5J.ThreeAtFreePaid
import Johnson.Desc.Kinds.Law.HeadCutsFive
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws

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

open VerifiableInference.PlanWritten (madeRow keyOfScan fullKey)

/-- **`h.Three h.free` from one row of tests, two closed conditions and one fact on reached
states.** -/
theorem three_at_free_row
    (hr : (!Decidable.decide (keyOfScan Zp.p.X.P = fullKey) || madeRow Zp) = true)
    {L : Laid} {M : List OracleShape} {nW : ℕ}
    (hEnd : ∀ z s, h.toAtMg.typed z →
      Reach 0 (cF.blocksInOrder.map VerifiableInference.Desc.Sound.below) (ProofFile.startS Zp) 358 (z, s) →
      s.failed = none → seatsCarriedB L s.book = true ∧ msgShapesB M s.st = true)
    (T : PlanSits L M (LLT25.vAt Zp (At.N Zp cF)) (At.N Zp cF).indexNo nW)
    (hNum : (At.N Zp cF).msgsAt none = nW + wMsgs Zp) : h.Three h.free :=
  three_at_free_paid h
    (by exact VerifiableInference.Desc.Kinds.Head.Law.head_cuts_of_guard h hr)
    (VerifiableInference.PlanWritten.pinnedAt_of_row hr) hEnd T hNum

end P5J

#print axioms P5J.three_at_free_row
