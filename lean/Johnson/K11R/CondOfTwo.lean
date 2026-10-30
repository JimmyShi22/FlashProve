-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/K11R/CondOfTwo.lean: WHAT IS LEFT BENEATH THE KIND K11's OWN SENTENCE (the merge of the claims
on the committed table) when the seven facts on the letters are drawn from the head too.
One structure, four theorems:
calls and joinings.

What is said.
  `K11Two h Bs`: TWO NAMED CONDITIONS, NEITHER OF WHICH READS A STATE: pendAll (a closed test with
    code) and slots: the merge's number of slots is at most 8192, the length of the mask code of the
    segment's message with mask rows.
  `k11Eight_of_two`: at the members that `xAt` finds at (73, 2) and at the index masks' place:
    `K11Two` gives `K11Eight` (CondOfEight.lean) at k := 0, ni := 256: roomLeft, idxShape,
    idxRows, niIs, ellPow, inM, idxSeat by the theorems of those names in
    Johnson/Desc/Sound/K11Tests/LettersSevenInScope.lean; that the index
    masks' place is (1, 0) by `AtMg.seats_written` (Johnson/HB/LLHARD/MaskSeatWritten.lean) and the
    kernel; that their message's number is 4 by `indexNo_at_head` (Johnson/P5J/StartAtHead.lean) and
    the kernel.
  `k11_kind_two`: `h.Kind 𝔏 K11` (Johnson/P5J/RowsAtAll.lean) from the three lists' heads, tm, and
    `K11Two` at every opening.

Limits. NEITHER CONDITION IS SHOWN HERE. What is left here is laid further in CondOfOne.lean
(slots); the whole chain is typed as one in CondOfPend.lean. The head is the head with the
fourteen entry tests: `pins_of_laid` (Johnson/Goal/Skeleton/PinsOfLaid.lean), on which what falls
here rests (idxShape, idxRows, niIs, ellPow and inM are handed the laid value too, by `laidPOf_of`;
`index_at_head` spends it through `seats_written`), stands over the form of the proof file's entry
tests with fourteen rows, two of which are the comparisons with the written plan; the head's field
laid says that every entry test accepts. A verifier whose entry tests lack these two rows gives no
such head. A member of the head is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library
AtFullSide/Top/). Nothing on soundness.

-/
import Johnson.K11R.CondOfEight
import Johnson.Desc.Sound.K11Tests.LettersSevenInScope
import Johnson.HB.LLHARD.MaskSeatWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace K11

open OnBytes (OracleShape ceilLog2)
open OnBytes.PscRun (Sized)
open OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Block Chain KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf)
open VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Desc.K12.Door (Laid msgsOfChain)
open VerifiableInference.Desc.Sound.MgAt (mergeAt)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (WaK6)
open Johnson.Desc.First.Walk.Tied (Reach rowsBefore)
open Inst.Model (ppref)
open Inst.Model.Layout (kRef)
open P5J (AtMgA mgAtAll TS F0T Free)
open ProofFile (Cl)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **WHAT IS LEFT: TWO FACTS, NEITHER OF WHICH READS A STATE.** -/
structure K11Two (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase) : Prop where
  /-- a closed test, with code, off the public parameters alone -/
  pendAll : pendAllB (parOf Zp Bs.G₀).lay h.𝔇.d1.lin = true
  /-- the merge's slots are no more than the mask code is long -/
  slots : (parOf Zp Bs.G₀).nMsg ≤ 8192

/-- Under the head the index masks' place is (1, 0). -/
theorem index_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (P5J.At.N Zp cF).index = (1, 0) := by
  show (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).index = (1, 0)
  rw [(P5J.AtMg.seats_written h.toAtMg).2.2]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Under the head their message's number is 4. -/
theorem indexNo_four (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (P5J.At.N Zp cF).indexNo = 4 :=
  (P5J.indexNo_at_head h.toAtMg).trans (by decide +kernel)

set_option maxRecDepth 100000 in
/-- **With the seven facts on the letters drawn from the head.** -/
theorem k11Eight_of_two (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase)
    (xM xI : Mem) (hxM : xAt (P5J.At.ms Zp Z.lay) (73, 2) = some xM)
    (hxI : xAt (P5J.At.ms Zp Z.lay) (P5J.At.N Zp cF).index = some xI) (Q : K11Two h Bs) :
    K11Eight h Bs xM xI 0 256 := by
  have hy := (P5J.pins_of_laid h.scope h.laid).1
  have hl := LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks
  have hi := index_at_head h
  have hn := indexNo_four h
  rw [hi] at hxI
  exact
    { pendAll := Q.pendAll
      roomLeft := by
        show 0 < VerifiableInference.Desc.First.FillP1.free0Of (P5J.At.cs Zp)
          (msgsOfChain Zp.made.proof.1) (P5J.At.N Zp cF).indexNo - rowsBefore _ 24
        rw [hn]
        exact LT28.K11Tests.roomLeft_in_scope h.scope h.laid.pub hy _
      idxSeat := LT28.K11Tests.idxSeat_at hi hn
      idxShape := by
        show (msgsOfChain Zp.made.proof.1)[(P5J.At.N Zp cF).indexNo]? = _
        rw [hn]
        exact LT28.K11Tests.idxShape_in_scope h.scope h.laid.pub hy hl _ hxI
      idxRows := LT28.K11Tests.idxRows_in_scope h.scope h.laid.pub hy hl _ hxI
      niIs := LT28.K11Tests.niIs_in_scope h.scope h.laid.pub hy hl _ hxI
      ellPow := LT28.K11Tests.ellPow_in_scope h.scope h.laid.pub hy hl _ hxI
      inM := LT28.K11Tests.inM_in_scope h.scope h.laid.pub hy hl _ hxM Q.slots }

set_option maxRecDepth 100000 in
/-- **THE KIND K11's SHARE AT THE CLOSED CONSTANT, FROM `K11Two`.** -/
theorem k11_kind_two (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (tm : k11AtRB Zp 24 = true)
    (K : ∀ (Bs : ProofFile.PureBase) (base : List (Block S Cl)),
      IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
        (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np) →
      K11Two h Bs) :
    h.Kind 𝔏 KindName.K11 :=
  k11_kind_eight h 𝔏 q₁ q₂ q₃ tm fun Bs base O xM xI e2 e3 =>
    ⟨0, 256, k11Eight_of_two h Bs xM xI e2 e3 (K Bs base O)⟩

end K11

#print axioms K11.index_at_head
#print axioms K11.indexNo_four
#print axioms K11.k11Eight_of_two
#print axioms K11.k11_kind_two
