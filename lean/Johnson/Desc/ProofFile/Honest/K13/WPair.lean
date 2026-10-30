-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/WPair.lean: W's PLACE ("M:4": the place ⟨1, none, 4, K1⟩; at the
full size number 356 of the first chain: the library's `m4_written`,
Johnson/AtFull/Desc/Lots/K13LotRows.lean; `m4_place`, ExchangeM4At.lean of this folder): THE PAIR:
the job of kind K1's sending part at that place (`K1.wJobAt`, Honest/K1/PlaceW.lean) HANDED THE
FILLING OF W's MAIN ROWS (`wDataAt`, WData.lean of this folder): the address built of the plan's
place, part 0 and message 0 is the filling's; WHAT THE JOB's DATA ARE, as an equation without
hypothesis: in it the job is seen to ask at that address; and the filling lays data only at a main
row and a place that the sending's message 0 has. Three statements with their proofs; no definition.
General in the filler of the pile, the public data, the list of messages, the number of the first
message, the input and what stands in front: no hypothesis on a proof file, no closed fact.

Main names: `wPair_addr`: **part 0, message 0 of the place of the library's plan of W's sending at
piece 4 is `wAddr`.** `wPair_data`: **at message 0, where the filling lays: W's entry (`wVec`);
everywhere else: nothing.** `wPair_lays_in_shape`: **where the shape has a message with W (hm) and
the filling lays data: the row lies below message 0's number of main rows, the place below the
message length of its code at the sending's own codes.**

Why. The job and the filling stand in two folders; nothing else ties them. Here Lean holds that they
meet. THE TYPE: the left side of `wPair_data` is a term only if the filling has the type that the
job takes. THE ADDRESS: that the JOB asks at the filling's address is held inside `wPair_data` alone
(its right side lays at message 0 and at `wAddr`); `wPair_addr` names no job: it says that the
address built of the plan's place, part 0 and message 0 is `wAddr`. THE SHAPE:
`wPair_lays_in_shape`, in the sender's own terms: the text that lays a message's rows (`rowsR`,
Honest/K1/Coins.lean) reads `shapeAt P k` and `P.codes.base.getD s.code default`, and yields 0 from
that number of main rows, and from that length, on.

Two folders are called K1. In this file `K1.wJobAt`, `K1.wGp`, `K1.PlaceIn` and `K1.w_shape_zero`
are the honest side's (`ProofFile.Honest.K1`, Honest/K1/); the plan `parW` is the library's and is written
with its whole name (`VerifiableInference.Desc.K1.parW`, Johnson/Desc/K1/Places.lean).

How. `wPair_addr`: by definition. `wPair_data`: by unfolding (`wJobAt`, `placeJob`,
`RowData.forSend`, `RowData.at_`), a case on the message's number, `wData_at` and `wData_other`
(WData.lean). `wPair_lays_in_shape`: K1's `w_shape_zero` (Honest/K1/Law/ShapeAtW.lean: message 0 of
the plan has W's shape); the plan's codes are the parameters' by its text; `lays` unfolded.

Limits. `wPair_data` SAYS WHAT THE DATA ARE, NOT WHAT THEY MEAN: the job reads through
`RowData.at_`: WHERE `RowData.readyAt` REJECTS AT THE LIST HEARD THE VALUE MEANS NOTHING, and the
equation holds there too; a sentence "it is W" would name `readyAt`. It holds at an empty list of
messages too: "message 0" is the number at which the data are asked. WHETHER `lays` ACCEPTS ANYWHERE
IS LEFT OPEN HERE: under the library's head (the hypothesis `P5J.AtMgA`: the full size and the
format's second hash function alone) it accepts at 2^kCol places (`k13_wLays_at_head`,
AtFullSide/K13/WFillAtHead.lean); WDataToy.lean evaluates `wData` at a toy's typed numbers, not
`wDataAt` at public data. Where it accepts nowhere, `wPair_data` has "nothing" on both sides and
`wPair_lays_in_shape` is idle. That hm can hold: at the full size it is the library's `wMsg_written`
(Johnson/HB/LLHARD/PlanAtQFull.lean). Piece 4 is typed: where the pile has one row there is no
batching, W's place is another and the filling lays nothing (the head of WData.lean). That the part
sends what the data yield is the sending part's text, not treated here. The data are values of the
extension field (the arm `.inr` of the sum of the two fields); THAT W's MAIN ROWS ARE OVER THAT
FIELD (the shape's mainDeg is 3) IS NOT SAID HERE (under the library's head: `k13_wShape_at_head`,
the same file): where they are not, `rowsR` lays 0 for them in the extension field's rows. That the
filler yields the verifier's pile's weights and points: not claimed (the head of WData.lean); that
the filling's number of challenges is the number of rounds in front of the place: not here (under
the library's head it is the number of rounds in front of number 356 of the first chain:
`k13_wHeard_is_rounds`, the same file). Nothing on mask rows, rows' tails or a pad's places. No side
is laid here: which list of halves a filling holds is the frame's. Nothing outside this file calls
these statements.

What is not claimed. It is none of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.WData
import Johnson.Desc.ProofFile.Honest.K1.Law.ShapeAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes OnBytes.Params
open Johnson.Prover.Send (shapeAt)

variable {Xi : Type}

/-- **THE ADDRESS**: part 0, message 0 of the place of the library's `parW` at piece 4 is `wAddr`.
-/
theorem wPair_addr (q : Params.First) (gp : _root_.Desc.Plain.GPar) (msg : Array OracleNotice) :
    (⟨⟨(VerifiableInference.Desc.K1.parW q gp 4 msg).place, 0⟩, 0⟩ : MsgAddr) = wAddr :=
  rfl

/-- **THE PAIR AT W's PLACE: WHAT THE JOB's DATA ARE.** The job of K1's sending part at W's place
(`K1.wJobAt`, Honest/K1/PlaceW.lean), handed the filling `wDataAt pile` (WData.lean of this folder):
at message 0, where the filling lays: W's entry; everywhere else: nothing. WHERE `readyAt` REJECTS
AT THE LIST HEARD THE VALUE MEANS NOTHING: the job reads through `at_`. -/
theorem wPair_data {X : Type} (pile : Pub → Ground → PileOf Xi) (Z : Pub) (G : Ground)
    (msg : Array OracleNotice) (first : Nat) (w : K1.PlaceIn Xi) (fr : Front X) (k r j : Nat) :
    (K1.wJobAt (X := X) Z.first (K1.wGp Z) 4 msg first (wDataAt pile Z G)).data w fr k r j =
      if k = 0 ∧ (wDataAt pile Z G w.x).lays wAddr r j = true then
        some (.inr (wVec Z.first.lin w.R.weights
          (wG Z.first.lin (wHeard Z) (pile Z G) w.x (fr.heard.take (wHeard Z)))
          (wNo Z.first.codes Z.first.lin r j)))
      else none := by
  show (wDataAt pile Z G w.x).at_ w.R fr.heard ⟨⟨⟨1, none, 4, .K1⟩, 0⟩, k⟩ r j = _
  by_cases hk : k = 0
  · subst hk
    show (wDataAt pile Z G w.x).at_ w.R fr.heard wAddr r j = _
    by_cases hl : (wDataAt pile Z G w.x).lays wAddr r j = true
    · rw [if_pos ⟨rfl, hl⟩]
      exact wData_at _ _ _ _ _ _ _ _ _ _ _ hl
    · rw [if_neg fun q => hl q.2]
      unfold RowData.at_
      rw [if_neg hl]
  · rw [if_neg fun q => hk q.1]
    have ha : (⟨⟨⟨1, none, 4, .K1⟩, 0⟩, k⟩ : MsgAddr) ≠ wAddr := fun e =>
      hk (congrArg MsgAddr.msg e)
    unfold RowData.at_
    rw [if_neg (by rw [show (wDataAt pile Z G w.x).lays _ r j = false from
      wData_other _ _ _ _ _ _ _ _ _ ha]; exact Bool.false_ne_true)]

/-- **WHERE THE FILLING LAYS DATA THE SENDER HAS A MAIN ROW AND A PLACE**, where the shape has a
message with W (hm): the row lies below the number of main rows of the sending's message 0, the
place below the message length of that message's code at the sending's own codes. -/
theorem wPair_lays_in_shape (pile : Pub → Ground → PileOf Xi) (Z : Pub) (G : Ground) (x : Xi)
    {msg : Array OracleNotice} (hm : linMessageW Z.first.lin = some msg) {r j : Nat}
    (h : (wDataAt pile Z G x).lays wAddr r j = true) :
    r < (shapeAt (VerifiableInference.Desc.K1.parW Z.first (K1.wGp Z) 4 msg) 0).mainRows ∧
      j < ((VerifiableInference.Desc.K1.parW Z.first (K1.wGp Z) 4 msg).codes.base.getD
        (shapeAt (VerifiableInference.Desc.K1.parW Z.first (K1.wGp Z) 4 msg) 0).code
        default).ell := by
  rw [K1.w_shape_zero Z.first (K1.wGp Z) 4 msg hm]
  have h' : (wAddr == wAddr && wPublic Z.first.codes Z.first.lin (wHeard Z) Z.first.pendingRows &&
      decide (r < Z.first.lin.w.mainRows) && decide (j < wEll Z.first.codes Z.first.lin) &&
      decide (wNo Z.first.codes Z.first.lin r j < 2 ^ Z.first.lin.kCol)) = true := h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
  exact ⟨h'.1.1.2, h'.1.2⟩

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.wPair_addr
#print axioms ProofFile.Honest.K13.wPair_data
#print axioms ProofFile.Honest.K13.wPair_lays_in_shape
