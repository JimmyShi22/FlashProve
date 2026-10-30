-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K1/OpeningSeatsK4.lean: THE SHARED "SENDING" (the kind K1) AGAINST THE NUMBERS AT WHICH
THE FEED-FORWARD LAYERS' OWN ROUNDS (the kind K4) READ THE OPENING's MESSAGES NUMBER 0 AND NUMBER 4.
For the authors of K4's lots, whose laws take of the sender's lot: "its number is k4MaskNum Zp
(2 * g)", and entries that lie below the sender's mask rows' length. PUBLIC DATA ALONE: seats,
numbers of messages, counts of segments, lengths: where a message sits and which entry is read,
never what stands in it. Eleven theorems; NO DEFINITION. A TRIAL THAT COUNTS IN NO COLUMN.
NO PROPERTY IS CLAIMED.

IT STANDS OVER TWO FILES OF ANOTHER HOUSE, definitions alone:
Johnson/Desc/ProofFile/Honest/K4/Lot/MaskNum.lean (k4MaskPos, k4MaskSeat, k4MaskNum) and
Johnson/Desc/ProofFile/Honest/K4/Lot/IndexNum.lean (k4IndexRows, k4IndexTakes).

At the written data:
  - maskHitW: the search inside k4MaskMsg, at segment 0, HITS, at index 0: it answers "some 0". By
    evaluation in Lean's kernel. maskHitW_miss: at number 25 it answers "none" (whether for want of
    a link of that number, or of a message with mask rows there, is not said): so the text has the
    default's case, which the number 0 alone does not tell from a hit.
  - maskSeatPickW: of the opening's five messages, number 0 alone has as its seat (seatOfMsg
    K1.parGF 0 n) the seat that the written plan gives segment 0's first message with mask rows. By
    evaluation in Lean's kernel. IT IS ITS OWN NEGATIVE TEST: the other four are shut out.
  - idxRowsW: the written list of shapes has one mask row at number 4. By the library's msgs_sorted
    (Johnson/Road/K4/K4PinsSends.lean), then by evaluation.

Under h (the library's head: A HYPOTHESIS) and O, at the plan at the description's own ground
(K1.firstPar Bs.G₀.first (K1.gpOf Zp)):
  - maskHit_head (h alone): the search hits at index 0 at the public part's own request too.
  - maskSeat_zero: our seat of message number 0 at member number 2 is k4MaskSeat Zp 0.
  - maskNum_zero: so its number in the witness, k1Num, is k4MaskNum Zp (2 * 0): index_two's and
    k1Num_index's like (Johnson/Desc/ProofFile/Honest/K1/Law/K1NumAtHead.lean) for the mask row.
  - idxRows_head: k4IndexRows Zp is the number of mask rows of our message number 4 (both are 1).
  - idxTakes_head: at g below 12, k4IndexTakes Zp g = g: a call of the library's rowsBefore_at
    (Johnson/Road/K4/Riders/BuiltFvs.lean).
  - idxTakes_below: so it lies below the mask rows' entries of our message number 4 (256).
  - idxEntry_head: K4's row and place of that entry (k4IndexRow, k4IndexPlace) are the entry's
    number modulo, and divided by, OUR number of mask rows: the form of msgTxt_mask_slot
    (Johnson/Desc/ProofFile/Honest/K1/ScriptMaskSlot.lean).

Kin. The other house's maskSeatAt_written
(Johnson/Desc/ProofFile/Honest/K4/Law/W/MaskNumsApart.lean) has, under WrittenAt, that k4MaskSeat is
the written plan's seat. NOT IMPORTED; its three steps are gone again inside maskSeat_zero's proof,
over the library's own H2K5.Door.seatCalls_shape, seatsAt_written, shape_one and written_of_head.

Limits. THE FULL SIZE ALONE. All but the four at the written data are CONDITIONAL on h and O
(maskHit_head on h alone), at the format's second hash function. SEGMENT 0 ALONE for the mask row: the
other eleven segments' messages are another sender's. That the entries which K4 reads of the mask
row of message number 0 lie below its 8192 entries (openingLens_head,
AtFullSide/K1/OpeningLengthsW.lean) is NOT said here: AtFullSide/K1/OpeningRoomK4.lean. Where no
message of a segment has mask rows k4MaskSeat's search answers its default in silence. maskSeatPickW
ALONE DOES NOT TELL A HIT FROM THAT DEFAULT, which are both 0 here: it shows that the seat so
answered is our number 0's and none of the other four's; that the search hits: maskHitW and
maskHit_head. That the message which it hits in the request's list is the sender's number 0 is said
through the seat alone.
Nothing on a run, or on what any coin is. Nothing on soundness, on completeness or on any other
property.
Terms: lean/GLOSSARY.md.
-/
import AtFullSide.K1.OpeningLengthsW
import Johnson.Desc.ProofFile.Honest.K1.Law.K1NumAtHead
import Johnson.Desc.ProofFile.Honest.K4.Lot.MaskNum
import Johnson.Desc.ProofFile.Honest.K4.Lot.IndexNum
import Johnson.Road.K4.K4HeadWritten
import Johnson.Road.K4.K4PinsSends
import Johnson.Road.K4.Riders.BuiltFvs
import Johnson.Desc.First.Att.Door.Law.K5WrittenPlans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K1
open ProofFile.Honest ProofFile.Honest.K1
open ProofFile.Honest.K4.Lot (k4MaskMsg k4MaskPos k4MaskSeat k4MaskNum k4IndexRows k4IndexTakes
  k4IndexRow k4IndexPlace)
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (messagesAt keptAt)
open VerifiableInference.Desc.K1 (parGF seatOfMsg)
open VerifiableInference.Desc.K12.Door (msgsOfChain)
open Johnson.Prover.Send (shapeAt)
open Johnson.G (proofSendsFull)
open OnBytes.Maker (WholeD)
open OnBytes.Road.K4 (sentW written_of_head shape_one seatsAt_written msgs_sorted)
open _root_.Desc.K14.Law (seatZ secondAt)

set_option maxRecDepth 1000000 in
/-- At segment 0 of the written request the search for a message with mask rows hits, at index
0. -/
theorem maskHitW : ((messagesAt sentW 0).findIdx? fun y => y.shape.maskRows != 0) = some 0 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The search can miss: at number 25 it finds none. Whether the written request has a link of that
number is not said. -/
theorem maskHitW_miss : ((messagesAt sentW 25).findIdx? fun y => y.shape.maskRows != 0) = none := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Of the opening's messages number 0 alone sits at the written plan's seat of segment 0's first
message with mask rows. -/
theorem maskSeatPickW : ((List.range parGF.sent.size).filter fun n =>
    decide (seatOfMsg parGF 0 n = P6T.seatCallsT P5T.psFull sentW 0 (k4MaskPos sentW 0))) =
      [0] := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The written list of shapes has one mask row at number 4. First the library's msgs_sorted (the
written sendings stand in the order of their entries): without that step the evaluation failed. -/
theorem idxRowsW : (((msgsOfChain proofSendsFull.1)[4]?).map (·.maskRows)).getD 0 = 1 := by
  rw [msgs_sorted]
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- h IS A PREMISE. At the public part's own request the search at segment 0 hits, at index 0: so
k4MaskMsg's 0 there is no default. -/
theorem maskHit_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ((messagesAt (P5J.At.sentAt Zp) 0).findIdx? fun y => y.shape.maskRows != 0) = some 0 := by
  have e : (P5J.At.sentAt Zp).shape = sentW.shape :=
    (written_of_head h.toAtMg).shape.trans shape_one
  have em : messagesAt (P5J.At.sentAt Zp) 0 = messagesAt sentW 0 := by
    unfold messagesAt
    rw [e]
  rw [em]
  exact maskHitW

/-- h AND O ARE PREMISES. **AT THE OPENING, MESSAGE NUMBER 0 SITS AT THE SEAT THAT THE PLAN GIVES
SEGMENT 0's FIRST MESSAGE WITH MASK ROWS**: k4MaskSeat Zp 0. That there is such a message:
maskHit_head. -/
theorem maskSeat_zero (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) 0 = k4MaskSeat Zp 0 := by
  have W := written_of_head h.toAtMg
  have e : (P5J.At.sentAt Zp).shape = sentW.shape := W.shape.trans shape_one
  have ep : k4MaskPos (P5J.At.sentAt Zp) 0 = k4MaskPos sentW 0 := by
    unfold k4MaskPos k4MaskMsg keptAt messagesAt
    rw [e]
  rw [seat_two_written h O 0]
  show seatOfMsg parGF 0 0 =
    P6T.seatCallsT (P5J.At.pseats Zp) (P5J.At.sentAt Zp) 0 (k4MaskPos (P5J.At.sentAt Zp) 0)
  rw [ep, H2K5.Door.seatCalls_shape e,
    show P5J.At.pseats Zp = P5T.psFull from seatsAt_written W]
  have hm : 0 ∈ (List.range parGF.sent.size).filter fun n =>
      decide (seatOfMsg parGF 0 n = P6T.seatCallsT P5T.psFull sentW 0 (k4MaskPos sentW 0)) := by
    rw [maskSeatPickW]
    exact List.mem_singleton.2 rfl
  exact of_decide_eq_true (List.mem_filter.1 hm).2

/-- h AND O ARE PREMISES. **SO ITS NUMBER IN THE WITNESS IS K4's NUMBER OF SEGMENT 0's MASK ROW's
MESSAGE**, in the form in which K4's laws take it of the sender's lot, at g := 0. -/
theorem maskNum_zero (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    k1Num Zp cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) 0 = k4MaskNum Zp (2 * 0) := by
  show P5J.At.arr Zp (seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) 0).1
      (seatAtMember cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) 0).2 =
    P5J.At.arr Zp (k4MaskSeat Zp 0).1 (k4MaskSeat Zp 0).2
  rw [maskSeat_zero h O]

/-- h AND O ARE PREMISES. K4's number of mask rows of the index masks' message is ours at message
number 4. -/
theorem idxRows_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    k4IndexRows Zp = (shapeAt (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) 4).maskRows := by
  rw [(opening_head h O).2.2.2.2.1]
  unfold k4IndexRows
  rw [(written_of_head h.toAtMg).proof]
  exact idxRowsW

/-- h, O AND hg ARE PREMISES. The entry's number that K4 reads at group g is g. -/
theorem idxTakes_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) : k4IndexTakes Zp g = g :=
  OnBytes.Road.K4.Riders.rowsBefore_at h.scope h.reads O hg

/-- h, O AND hg ARE PREMISES. **THE ENTRY THAT K4 READS OF MESSAGE NUMBER 4 LIES BELOW THE MASK
ROWS' ENTRIES AT THE SENDER's SHAPE**: the premise of msgTxt_mask_slot and mask_in at n := 4. -/
theorem idxTakes_below (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) {g : ℕ} (hg : g < 12) :
    k4IndexTakes Zp g < (shapeAt (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) 4).maskRows *
      ((K1.firstPar Bs.G₀.first (K1.gpOf Zp)).codes.mask.getD
        (shapeAt (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) 4).maskCode default).ell := by
  rw [idxTakes_head h O hg, (openingLens_head h O).2]
  omega

/-- h AND O ARE PREMISES. K4's row and place of the entry, by our number of mask rows. -/
theorem idxEntry_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) (g : ℕ) :
    k4IndexRow Zp g =
        k4IndexTakes Zp g % (shapeAt (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) 4).maskRows ∧
      k4IndexPlace Zp g =
        k4IndexTakes Zp g / (shapeAt (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) 4).maskRows := by
  unfold k4IndexRow k4IndexPlace
  rw [idxRows_head h O]
  exact ⟨rfl, rfl⟩

end AtFullSide.K1

#print axioms AtFullSide.K1.maskHitW
#print axioms AtFullSide.K1.maskHitW_miss
#print axioms AtFullSide.K1.maskSeatPickW
#print axioms AtFullSide.K1.idxRowsW
#print axioms AtFullSide.K1.maskHit_head
#print axioms AtFullSide.K1.maskSeat_zero
#print axioms AtFullSide.K1.maskNum_zero
#print axioms AtFullSide.K1.idxRows_head
#print axioms AtFullSide.K1.idxTakes_head
#print axioms AtFullSide.K1.idxTakes_below
#print axioms AtFullSide.K1.idxEntry_head
