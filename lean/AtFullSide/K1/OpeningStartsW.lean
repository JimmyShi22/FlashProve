-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K1/OpeningStartsW.lean: THE SHARED "SENDING" (the kind K1): THE OPENING's PLACE AND ITS
TWO STARTS, EACH AS ONE EQUATION, AGAINST THE MAKER's WRITTEN VALUES. For a spender's authors, who
ask: is the sender's place the written owner's; is the sender's own start the written base; has the
message one mask row; does number 4 lie below the plan's number of messages. PUBLIC DATA ALONE:
places, plans, counts, addresses: where a run of coins begins, never what stands in it. Six
theorems; NO DEFINITION. A TRIAL THAT COUNTS IN NO COLUMN.
NO PROPERTY IS CLAIMED.

At the written data (K1.parGF with the ride rideOf (firstFold K1.qFull)):
  - idxOwnerJoint, idxStartJoint: the written index-mask message rawIdxW
    (AtFullSide/K14/RawFactsWritten.lean): its owner is ⟨K1.parGF.place, 0⟩ (by evaluation in Lean's
    kernel); its start among the coins of E is our maskStart at message number 4 (a call).
  - idxStartJoint_bent: A NEGATIVE TEST: at message number 3 that joint is false.
  - maskRowsW: message by message, the number of mask rows: 1, 0, 0, 1, 1: so one at number 0 and
    one at number 4. By evaluation in Lean's kernel.
NOT TYPED ANEW: that the start at number 4 is 8647: k1StartW; the same under the head: k1Start_head
(both called here); that number 4 alone starts there: k1StartW_alone (not called): all three in
Johnson/Desc/ProofFile/Honest/K1/Law/StartAtFour.lean · that the plan has five messages: a
clause of sizes_two (Johnson/Desc/K1/Law/TiesWritten.lean; called here).
The like at message number 0 (owner, start, and that the start is 0) stands in
AtFullSide/K1/SegmentZeroJoints.lean: ownerJoint, startJoint, startZero.

Under h (the library's head: A HYPOTHESIS) and O:
  - opening_head: the plan and the ride at the description's own ground (K1.firstPar Bs.G₀.first
    (K1.gpOf Zp); rideOf (firstFold Bs.G₀.first)) have: that place; the starts 0 and 8647 at numbers
    0 and 4; one mask row at each; five messages.
  - opening_head_written: the same place and starts, said against the two written values: rowZeroW
    (AtFullSide/K1/SegmentZeroAtWritten.lean; the first member of the written rows) and rawIdxW.

Kin. The five starts and the five shapes' numbers are not laid here as lists over two senders;
here each
fact is one equation. Our idxOwnerW (Johnson/Desc/ProofFile/Honest/K1/Law/OwnerAtWritten.lean) says
of the maker's SEARCH what idxOwnerJoint and idxStartJoint say of the written VALUE; so, under the
head, do idxOwnerW_head (the same file) and rowOwnerW_head
(Johnson/Desc/ProofFile/Honest/K1/Law/RowOwnerAtWritten.lean; not imported) beside
opening_head_written.

Limits. THE FULL SIZE ALONE. The two last are CONDITIONAL on h and O, at the format's second hash function.
That rawIdxW and the written rows are what the maker's search returns: rawIdx_written and
rawRows_written (AtFullSide/K14/RawFactsWritten.lean); that rowZeroW is the first of these rows:
rowZeroW_written. Nothing on a run, or on what any coin is. Nothing on soundness, on completeness or
on any other property.
Terms: lean/GLOSSARY.md.
-/
import AtFullSide.K1.SegmentZeroJoints
import Johnson.Desc.ProofFile.Honest.K1.Law.StartAtFour
import Johnson.Desc.K1.Law.TiesWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K1
open ProofFile.Honest ProofFile.Honest.K1
open AtFullSide.K14
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (parGF)
open Johnson.Prover.Send (shapeAt)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)

/-- The written index-mask message's owner is the opening's sender, by the plan's own place. -/
theorem idxOwnerJoint : rawIdxW.owner = ⟨parGF.place, 0⟩ := by decide +kernel

/-- Its start among the coins of E is our maskStart at message number 4: k1StartW, read the other
way: the written value's number is 8647 by its text. -/
theorem idxStartJoint : rawIdxW.base.e = maskStart parGF (rideOf (firstFold K1.qFull)) 4 :=
  k1StartW.symm

set_option maxRecDepth 1000000 in
/-- The joint can fail: at message number 3 it is false. -/
theorem idxStartJoint_bent :
    decide (rawIdxW.base.e = maskStart parGF (rideOf (firstFold K1.qFull)) 3) = false := by
  decide +kernel

/-- Message by message: the number of mask rows. -/
theorem maskRowsW : ((List.range parGF.sent.size).map fun n => (shapeAt parGF n).maskRows) =
    [1, 0, 0, 1, 1] := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- h AND O ARE PREMISES. **THE OPENING's PLAN AT THE DESCRIPTION's OWN GROUND: ITS PLACE; ITS
STARTS AT NUMBERS 0 AND 4; ONE MASK ROW AT EACH; FIVE MESSAGES.** The first clause needs neither
premise: it holds by unfolding. The third is k1Start_head. -/
theorem opening_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).place = ⟨1, some 0, 1, .K1⟩ ∧
      maskStart (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) (rideOf (firstFold Bs.G₀.first)) 0 = 0 ∧
      maskStart (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) (rideOf (firstFold Bs.G₀.first)) 4 = 8647 ∧
      (shapeAt (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) 0).maskRows = 1 ∧
      (shapeAt (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) 4).maskRows = 1 ∧
      (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size = 5 := by
  refine ⟨?_, ?_, k1Start_head h O, ?_, ?_, ?_⟩
  · rfl
  · rw [K1.eG_atAll h O (K1.pin1_atAll h),
      firstFold_shape (q' := K1.qFull) ((K1.hs_atAll h O (K1.pin1_atAll h)).trans ?_)]
    · exact startZero
    · rfl
  · rw [K1.eG_atAll h O (K1.pin1_atAll h)]
    decide +kernel
  · rw [K1.eG_atAll h O (K1.pin1_atAll h)]
    decide +kernel
  · rw [K1.eG_atAll h O (K1.pin1_atAll h)]
    exact VerifiableInference.Desc.K1.sizes_two.2.1

/-- h AND O ARE PREMISES. **THE SENDER's PLACE IS THE WRITTEN OWNER's, AND ITS OWN START THE WRITTEN
BASE, AT BOTH WRITTEN VALUES.** -/
theorem opening_head_written (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    rowZeroW.owner = ⟨(K1.firstPar Bs.G₀.first (K1.gpOf Zp)).place, 0⟩ ∧
      rowZeroW.base.e =
        maskStart (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) (rideOf (firstFold Bs.G₀.first)) 0 ∧
      rawIdxW.owner = ⟨(K1.firstPar Bs.G₀.first (K1.gpOf Zp)).place, 0⟩ ∧
      rawIdxW.base.e =
        maskStart (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) (rideOf (firstFold Bs.G₀.first)) 4 := by
  obtain ⟨hp, h0, h4, -, -, -⟩ := opening_head h O
  rw [hp, h0, h4]
  exact ⟨rfl, rfl, rfl, rfl⟩

end AtFullSide.K1

#print axioms AtFullSide.K1.idxOwnerJoint
#print axioms AtFullSide.K1.idxStartJoint
#print axioms AtFullSide.K1.idxStartJoint_bent
#print axioms AtFullSide.K1.maskRowsW
#print axioms AtFullSide.K1.opening_head
#print axioms AtFullSide.K1.opening_head_written
