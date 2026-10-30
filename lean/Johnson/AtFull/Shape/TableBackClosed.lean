-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/TableBackClosed.lean: UNDER THE HEAD P5J.AtMgA THE TABLE's STEPS ON SHAPES AND
ITS TESTS ON VALUES AT MEMBERS 354, 355 AND 356 OF THE FIRST CHAIN (the chain's last proximity test;
the members' batching; W's sending; `Tab.g`, `Tab.vals`, TableOfSteps.lean) HAVE NO LETTER OF THE
PUBLIC PART Zp OR OF THE GROUND G. Three laws; rewritings; nothing is evaluated here.

What it is for. The rule's public premise "the run on shapes returns" is a closed Bool only where
each step's letters are closed. Here three steps more have none.

How. The table's cells behind the links are the back row's (`cells_back`, TableFrames.lean). Its
second reads `H2U.p12OfMade Z.made`, under the head the written member (`p12_at_head`,
TestNumbersAtHead.lean). Its third reads `K13.whereOf Z`, under the head the written record
(`where13_at_head`, BackNumbersAtHead.lean). Its fourth reads that record, what goes out with W at
Z.first's linear shape, and W's sending's numbers `wPar`, which read Z.first's codes and shape and
Z.P: all written under the head (`first_at_head`, `par_at_head`); what goes out at the written
linear shape is the library's `wMsgFull` (`wMsg_written`, Johnson/HB/LLHARD/PlanAtQFull.lean).

Main names.
* **`tab_354_closed`**: Tab.g Zp G 354 = optE of "if testGuardB piLFull y.1 then testA piLFull y
  else nothing", and Tab.vals Zp G 354 = testV piLFull.
* **`tab_355_closed`**: Tab.g Zp G 355 = liftO (battGS where13W); no test on values.
* `wParW msg`, `wPar_at_head`. **`tab_356_closed`**: Tab.g Zp G 356 = sendWA (wParW wMsgFull)
  where13W; no test on values.

Limits. UNDER THE HEAD: that it has a member is shown in scope, where the reader returns and
`protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at
two named sets of public files, in a side library. NOTHING ON WHETHER A GUARD ACCEPTS, OR A STEP
RETURNS, AT ANY SHAPE: that belongs to "the run on shapes returns". Nothing on whether a test on
values accepts at any state. where13W's last field is a closed sum that is not evaluated. The second
halves at 355 and 356 ("no test on values") need no head: there the premise is idle. Three of 358
members. The full size alone. At the format's second hash function. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.TableSwitch
import Johnson.AtFull.Shape.TestNumbersAtHead
import Johnson.AtFull.Shape.BackNumbersAtHead
import Johnson.HB.LLHARD.PlanAtQFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Desc.K13.Law (wMsgFull wMsg_written)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **UNDER THE HEAD THE TABLE's STEP AND ITS TEST ON VALUES AT 354 HAVE NO LETTER OF THE PUBLIC
PART OR OF THE GROUND.** -/
theorem tab_354_closed (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) :
    Tab.g Zp G 354 = (optE fun y =>
        if testGuardB H2K.Member.piLFull y.1 then testA H2K.Member.piLFull y else none) ∧
      Tab.vals Zp G 354 = testV H2K.Member.piLFull := by
  have hc : Tab.cells Zp G 354 = (Tab.backRow Zp G).at 1 := cells_back Zp G 1 rfl
  have e := p12_at_head h.toAtMg
  constructor
  · rw [cell_g hc]
    show (optE fun y =>
      if testGuardB (H2U.p12OfMade Zp.made) y.1 then testA (H2U.p12OfMade Zp.made) y else none) = _
    rw [e]
  · funext s rs gs
    rw [cell_v hc]
    show testV (H2U.p12OfMade Zp.made) s rs gs = _
    rw [e]

/-- The numbers of W's sending, written; msg: what goes out. -/
def wParW (msg : Array OracleNotice) : VerifiableInference.Desc.K1.Par :=
  { place := ⟨1, none, 4, .K1⟩, codes := proofSizedFull.codes,
    gp := { samples := proofSizedFull.request.answers, firstTree := 0 }, work := 0,
    parts := [("W and the messages sent with it", msg)],
    groups := VerifiableInference.Desc.K1.inGroup
      (proofSizedFull.request.link.length + proofSizedFull.request.last.length) msg }

/-- Under the head the numbers of W's sending are the written ones. -/
theorem wPar_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (msg : Array OracleNotice) :
    wPar Zp msg = wParW msg := by
  obtain ⟨f1, -, f3, -, -, -⟩ := first_at_head h.toAtMg
  have hP := par_at_head h.toAtMg
  have e : wPar Zp msg =
      { place := ⟨1, none, 4, .K1⟩, codes := Zp.first.codes,
        gp := { samples := Zp.P.samples, firstTree := Zp.P.firstTree }, work := 0,
        parts := [("W and the messages sent with it", msg)],
        groups := VerifiableInference.Desc.K1.inGroup
          (Zp.first.shape.link.length + Zp.first.shape.last.length) msg } := rfl
  rw [e, f1, f3, hP]
  rfl

/-- **UNDER THE HEAD THE TABLE's STEP AT 355 HAS NO LETTER OF THE PUBLIC PART OR OF THE GROUND.** -/
theorem tab_355_closed (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) :
    Tab.g Zp G 355 = liftO (battGS where13W) ∧ Tab.vals Zp G 355 = noVals := by
  have hc : Tab.cells Zp G 355 = (Tab.backRow Zp G).at 2 := cells_back Zp G 2 rfl
  constructor
  · rw [cell_g hc]
    show liftO (battGS (VerifiableInference.Desc.K13.whereOf Zp)) = _
    rw [where13_at_head h.toAtMg]
  · funext s rs gs
    rw [cell_v hc]
    rfl

/-- **THE LIKE AT 356**, at what goes out with W at the written linear shape. -/
theorem tab_356_closed (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) :
    Tab.g Zp G 356 = sendWA (wParW wMsgFull) where13W ∧ Tab.vals Zp G 356 = noVals := by
  obtain ⟨-, f2, -, -, -, -⟩ := first_at_head h.toAtMg
  have hm : linMessageW proofSizedFull.batch.shape = some wMsgFull := wMsg_written
  have hc : Tab.cells Zp G 356 = (sendWA (wParW wMsgFull) where13W, noVals) := by
    rw [cells_back Zp G 3 rfl]
    show Tab.sendW Zp = _
    unfold Tab.sendW
    rw [f2, hm]
    show (sendWA (wPar Zp wMsgFull) (VerifiableInference.Desc.K13.whereOf Zp), noVals) = _
    rw [wPar_at_head h, where13_at_head h.toAtMg]
  constructor
  · rw [cell_g hc]
  · funext s rs gs
    rw [cell_v hc]

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.tab_354_closed
#print axioms Johnson.AtFull.Shape.wPar_at_head
#print axioms Johnson.AtFull.Shape.tab_355_closed
#print axioms Johnson.AtFull.Shape.tab_356_closed
#print axioms Johnson.AtFull.Shape.wParW
