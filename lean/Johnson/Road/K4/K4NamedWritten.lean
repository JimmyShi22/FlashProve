-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Road/K4/K4NamedWritten.lean: TWO OF THE NINE NAMED TESTS OF K4's ROW (the structure
K4NamedW, Johnson/Road/K4/K4RowAtWide.lean) AT THE COMPOSED MEANING's CLOSED CONSTANT, AS CLOSED
FACTS BY LEAN's KERNEL AT WRITTEN VALUES, EACH WITH ITS TIE: room1 and maskP. One definition, four
closed facts, five theorems without an evaluation.

  `dW`: the plan's side of what is sent, at the written request's shape and the written numbers;
    its looks of arrays are empty: the test does not read them.
  `maskSeat_written`: BY THE KERNEL: at the written values the seat of the message with segment
    2 g's mask row is there, at all twelve groups. NEGATIVE TESTS: `maskSeat_written_no` (the
    next segment's own tenants: nothing at all twelve) · `maskSeat_written_no'` (the count of
    messages sent is the one in front of the GROUP BEFORE's place of K4: nothing at all eleven
    later groups: the segment's own first message is not sent yet there).
  `maskSeat_trees`: the test does not read the looks of arrays (rfl).
  `base_written`: the counts "how many messages are sent in front of a segment" are the written
    ones, where the numbers' field msgsAt is.
  `maskP_const`: the field maskP at the constant, g < 12. Premises: hA (for the constant's name) ·
    W : WrittenAt Zp · hc: the first chain's cut is the written one · hL: L is what the
    reader of the chain's listed seats (`P5J.At.laid?`) returns.
  `room1_const`: the field room1 at the constant, g < 12: 1 ≤ 255 - g. Premises: hA · an opening O ·
    W · hc. By room1_of_fill (Johnson/Road/K4/K4RowWideScope.lean) at k4Fill_all, and the
    closed fact free0_written (Johnson/Road/K4/K4PinsWrittenNext.lean). NEGATIVE TESTS:
    `free0_written_no` (BY THE KERNEL: the message ONE FURTHER than the index masks' has no free
    entry) · `room1_written_no` (so, were the numbers' message number one more, room1 would
    reject at the first group already).
WHO PAYS W AND hc: the rows madeRow and cutRow of the verifier's entry tests
(Johnson/Desc/Laid/ProofAsks.lean) compare them, and under the head (a member of the head is proved
at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library AtFullSide/Top/)) both are theorems
(`written_of_head`, `cut_of_head`, Johnson/Road/K4/K4HeadWritten.lean); in
this file they are premises: conditions on the three public files alone.
Limits. The written values rest on prints of Lean's evaluator (their files' heads). The full size
alone. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.K4PinsWrittenNext
import Johnson.Road.K4.K4FillAll
import Johnson.Desc.First.RecordPlan
import Johnson.Desc.First.SentTerms

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes.Maker (WholeD)
open VerifiableInference.PlanWritten (proofSizedFull cutFirstFull)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S Numbers flatPlacesOf FillP1.free0Of)
open VerifiableInference.Desc.First.FillSent (SentData TreeLook sentDataOf sentDataAt baseAt)
open VerifiableInference.Desc.First.RecordPlan (maskSeatP)
open VerifiableInference.Desc.Sound (linksFull)
open Johnson.Desc.First.Walk.Tied (rowsBefore)

/-- The plan's side of what is sent, at the written values. -/
def dW : SentData :=
  sentDataOf proofSizedFull.request (baseAt nW linksFull (flatPlacesOf linksFull true)) fun _ => []

set_option maxRecDepth 1000000 in
/-- **At the written values the mask row's message has its seat, at all twelve groups.** -/
theorem maskSeat_written :
    (laidW?.any fun L => (List.range 12).all fun g =>
      (maskSeatP proofSizedFull.request dW (nW.sent (2 * g) 0) L.places
        (nW.msgsAt (flatPlacesOf linksFull true)[28 * g + 4]?) (2 * g)).isSome) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: at the next segment's own tenants there is none, at all twelve groups. -/
theorem maskSeat_written_no :
    (laidW?.any fun L => (List.range 12).any fun g =>
      (maskSeatP proofSizedFull.request dW (nW.sent (2 * g + 1) 0) L.places
        (nW.msgsAt (flatPlacesOf linksFull true)[28 * g + 4]?) (2 * g)).isSome) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: with the count of messages that stands in front of the group before's place of
K4 there is none, at all eleven later groups. -/
theorem maskSeat_written_no' :
    (laidW?.any fun L => (List.range 11).any fun g =>
      (maskSeatP proofSizedFull.request dW (nW.sent (2 * (g + 1)) 0) L.places
        (nW.msgsAt (flatPlacesOf linksFull true)[28 * g + 4]?) (2 * (g + 1))).isSome) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test of room1: the message one further than the index masks' has no free entry. -/
theorem free0_written_no : FillP1.free0Of proofSizedFull.codes mW (nW.indexNo + 1) = 0 := by
  decide +kernel

/-- So, were the numbers' message number one more, room1 would reject at the first group already. -/
theorem room1_written_no :
    ¬ 1 ≤ FillP1.free0Of proofSizedFull.codes mW (nW.indexNo + 1) - 0 := by
  rw [free0_written_no]
  decide

/-- The test does not read the looks of arrays. -/
theorem maskSeat_trees (shape : OnBytes.Params.ReqShape) (base : ℕ → ℕ)
    (T T' : ℕ → List TreeLook) (own places : List (ℕ × ℕ)) (n m : ℕ) :
    maskSeatP shape (sentDataOf shape base T) own places n m =
      maskSeatP shape (sentDataOf shape base T') own places n m := rfl

/-- The counts in front of the segments read the numbers' field msgsAt alone. -/
theorem base_written {N : Numbers} (h : N.msgsAt = nW.msgsAt) :
    baseAt N linksFull (flatPlacesOf linksFull true) =
      baseAt nW linksFull (flatPlacesOf linksFull true) := by
  funext m
  unfold baseAt
  rw [h]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **UNDER hA, hL, W, hc (PREMISES): maskP at the constant.** -/
theorem maskP_const (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {L : VerifiableInference.Desc.K12.Door.Laid} (hL : P5J.At.laid? Zp = some L)
    (W : WrittenAt Zp) (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull)
    {g : ℕ} (hg : g < 12) :
    (maskSeatP hA.𝔇.sent.shape hA.𝔇.pubD.dS (hA.𝔇.N.sent (2 * g) 0) (eAll Zp cF L).d12.L.places
      (hA.𝔇.N.msgsAt (flatPlacesOf linksFull true)[28 * g + 4]?) (2 * g)).isSome = true := by
  have B := book_of_cut W hc
  have eS : P5J.At.shape Zp = proofSizedFull.request := W.shape.trans shape_one
  have eL : laidW? = some L := (laid_at W).symm.trans hL
  have K := maskSeat_written
  rw [eL] at K
  have K1 : ((List.range 12).all fun g =>
      (maskSeatP proofSizedFull.request dW (nW.sent (2 * g) 0) L.places
        (nW.msgsAt (flatPlacesOf linksFull true)[28 * g + 4]?) (2 * g)).isSome) = true := K
  have K2 := List.all_eq_true.1 K1 g (List.mem_range.2 hg)
  show (maskSeatP (P5J.At.shape Zp)
    (sentDataOf (P5J.At.shape Zp)
      (baseAt (P5J.At.N Zp cF) linksFull (flatPlacesOf linksFull true)) _)
    ((P5J.At.N Zp cF).sent (2 * g) 0) L.places
    ((P5J.At.N Zp cF).msgsAt (flatPlacesOf linksFull true)[28 * g + 4]?) (2 * g)).isSome = true
  rw [base_written B.msgsAt, B.sent, B.msgsAt, eS, maskSeat_trees _ _ _ (fun _ => [])]
  exact K2

/-- **UNDER hA, AN OPENING, W, hc (PREMISES): room1 at the constant.** -/
theorem room1_const (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (L : VerifiableInference.Desc.K12.Door.Laid) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (Desc.K14.Law.seatZ Zp Np) (Desc.K14.Law.secondAt Zp Np))
    (W : WrittenAt Zp) (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull)
    {g : ℕ} (hg : g < 12) :
    1 ≤ (eAll Zp cF L).dP.free0 - rowsBefore (eAll Zp cF L).dP.fvs (2 * g) := by
  refine room1_of_fill hA.scope hA.reads O hg (k4Fill_all hA L) ?_
  show 1 ≤ FillP1.free0Of (P5J.At.cs Zp) (P5J.At.d12 Zp L).M (P5J.At.N Zp cF).indexNo - g
  rw [show P5J.At.cs Zp = proofSizedFull.codes from W.codes, msgs_at W L,
    (book_of_cut W hc).indexNo, free0_written]
  omega

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.maskSeat_written
#print axioms OnBytes.Road.K4.maskSeat_written_no
#print axioms OnBytes.Road.K4.maskSeat_written_no'
#print axioms OnBytes.Road.K4.room1_written_no
#print axioms OnBytes.Road.K4.free0_written_no
#print axioms OnBytes.Road.K4.maskSeat_trees
#print axioms OnBytes.Road.K4.base_written
#print axioms OnBytes.Road.K4.maskP_const
#print axioms OnBytes.Road.K4.room1_const
