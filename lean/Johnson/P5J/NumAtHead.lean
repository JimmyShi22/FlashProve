-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/NumAtHead.lean: THE COUNT OF ORACLE MESSAGES UNDER THE HEAD: at the one head in front of
the composed meaning's constant (`AtMg`, Johnson/P5J/AtMg.lean): of the 199 oracle messages that the
first chain's sub-protocols tell, 197 stand in front of W's sending, and W's sending holds 2. FROM
THE HEAD ALONE, at every function o in the place of the second hash function.

What it is for. The joining statement `three_at_free_row` (Johnson/P5J/ThreeAtFreeRow.lean) has a
premise hNum : (At.N Zp cF).msgsAt none = nW + wMsgs Zp. Here it is a theorem at nW := 197.

WHAT THE THREE NUMBERS COUNT. `msgsAt none`: over all 358 sub-protocols of the first chain, over the
trees that each tells, the tenants: all oracle messages, sampled or not: 199:
`AtMg.msgs_end` (Johnson/P5J/PlanSitsCore.lean): called. 197: the number, from 0, of W's own oracle
message: as many are told in front of place 356, where W's sending stands. 2: W's sending's oracle
messages, off the linear shape: W and a mask. So the equation says that W's sending is the last that
the first chain tells.

WHICH HEAD. The head holds that every entry test of the proof file accepts. THIS FILE STANDS OVER
THE THIRTEEN ENTRY TESTS OF ProofAsksFirstThirteenTests.lean: it spends both rows that compare with written values
(`AtMg.cut_written`, `AtMg.made_accepts`, Johnson/P5J/NumbersAtHead.lean). The numerals are numbers
of the written values: they hold under the head because its tests compare with these.

  `told_front_w`, `told_front_w_rejects`; `w_msgs_written`, `w_msgs_rejects`: the closed facts and
    their negative tests, by evaluations in Lean's kernel (`decide +kernel`). `w_msgs_written` says
    "some 2": the default 0 in the text of `wMsgs` is not met.
  `AtMg.w_msgs`: 2.
  `AtMg.num_at_head_text`: **the equation**, with the text of `wMsgs Zp` spelled out: the file that
    names it (Johnson/Desc/Last/CountAtEnd.lean) is not imported here.
    OWED THERE: one line by rfl.
    (Where this and lean/THEOREM.md differ, the page holds.)

Limits. The full size alone. That a head can be had at given public files is not said. Nothing on
soundness.
-/
import Johnson.P5J.PlanSitsCore
import Johnson.Goal.Numbers.MadeInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open OnBytes OnBytes.Maker
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (msgsTold toldCut)
open VerifiableInference.PlanWritten (proofSizedFull)

/-! ## 1 The closed facts -/

set_option maxRecDepth 1000000 in
/-- In front of place 356 the written cut tells 197 oracle messages. -/
theorem told_front_w : msgsTold toldCut 356 = 197 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative tests: one place further on 199 stand in front, not 197; and with what place 356
tells struck out, 197 are told in all, not 199. -/
theorem told_front_w_rejects :
    (msgsTold toldCut 357, msgsTold (toldCut.set 356 []) 358) = (199, 197) := by decide +kernel

/-- At the written linear shape W's sending is there and holds two oracle messages. -/
theorem w_msgs_written : (linMessageW proofSizedFull.batch.shape).map (·.size) = some 2 := by
  decide +kernel

/-- The negative test: at the same shape without masks sent ahead it holds one. -/
theorem w_msgs_rejects :
    (linMessageW { proofSizedFull.batch.shape with masksAhead := false }).map (·.size) =
      some 1 := by decide +kernel

/-! ## 2 Under the head -/

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **W's sending holds two oracle messages**, off the linear shape as read back. The left side is
the text of `wMsgs Zp` (Johnson/Desc/Last/CountAtEnd.lean). -/
theorem AtMg.w_msgs (h : AtMg o Z D r Zp Np cF) :
    ((linMessageW Zp.first.lin).map (·.size)).getD 0 = 2 := by
  rw [(VerifiableInference.PlanWritten.Joined.first_written_in_scope h.scope h.laid.pub
    h.made_accepts).2.1, w_msgs_written]
  rfl

/-- **The count of oracle messages: W's sending is the last that the first chain tells.** -/
theorem AtMg.num_at_head_text (h : AtMg o Z D r Zp Np cF) :
    (At.N Zp cF).msgsAt none = 197 + ((linMessageW Zp.first.lin).map (·.size)).getD 0 := by
  rw [h.msgs_end, h.w_msgs]

end P5J

#print axioms P5J.told_front_w
#print axioms P5J.told_front_w_rejects
#print axioms P5J.w_msgs_written
#print axioms P5J.w_msgs_rejects
#print axioms P5J.AtMg.w_msgs
#print axioms P5J.AtMg.num_at_head_text
