-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/IndexLotInList.lean: THE WHOLE-MESSAGE LOT OF THE OPENING's
MESSAGE 4, WRITTEN AT THE NUMBER `k4IndexNum Zp` (as AtFullSide/K11/IndexLotCovered.lean writes the
sender's lot of the kind K11's second lot), IS A MEMBER OF K1's AUTHORS' OWN LIST OF LOTS
(`k1MsgLotsAt`, `k1MsgLots`, Honest/K1/LotsLaid.lean) AT THE OPENING's MEMBER, NUMBER 2 OF THE FIRST
CHAIN, WHERE THE LIST IS NUMBERED BY `P5J.At.arr Zp` AND THE JOB HAS THE GROUND's PLAN: UNDER THE
LIBRARY's HEAD AND THE OPENING. Three lemmas; no definition; none of the library's goals. PUBLIC
DATA ALONE: which message, never what stands in it.

Why. IndexLotCovered.lean left open whether the lot that K1's authors' list lays for message 4 bears
that number. K1's authors' answer: three files of theirs say it, short of one rewriting that was
typed by nobody. This is that rewriting.

  `four_is_index`
      message 4 is a message of the written opening, and its written seat is (1, 0): out of their
      `indexW`
  `openingLot_mem`
      the lot lies in `k1MsgLotsAt cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ (2, J)`; its number of
      challenges is theirs: front + roundsTo cF.blocksInOrder 2
  `openingLot_mem_list`
      so it lies in `k1MsgLots` at every list of jobs that holds (2, J)

By: `indexW`, `seat_two_written` (Honest/K1/Law/K1NumAtHead.lean) · `mem_k1MsgLots` (LotsLaid.lean):
theirs · `par_at_head` (IndexKeyWritten.lean of this folder).

WHAT IT IS NOT. NO LIST IS LAID: jobs, front, wit and own₀ are letters; that any filling lays (2, J)
with that plan is not said. Nothing on the lot's text.

Limits. One closed fact of K1's authors', by Lean's kernel, lies beneath. The full size; the
format's second hash function. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.K1NumAtHead
import Johnson.Desc.ProofFile.Honest.K1.LotsLaid
import Johnson.Desc.ProofFile.Honest.K11.Plays.IndexKeyWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (parGF seatOfMsg firstPar gpOf)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest.FirstThread (MsgLot)
open ProofFile.Honest.K1 (PlaceIn SendJob msgTxt k1MsgLotsAt k1MsgLots mem_k1MsgLots seatAtMember indexW
  seat_two_written)
open ProofFile.Honest.K4.Lot (k4IndexNum)

/-- **Message 4 is a message of the written opening, and its written seat is (1, 0).** -/
theorem four_is_index : 4 < parGF.sent.size ∧ seatOfMsg parGF 0 4 = (1, 0) := by
  have m : 4 ∈ (List.range parGF.sent.size).filter
      (fun n => decide (seatOfMsg parGF 0 n = (1, 0))) := by
    rw [indexW]
    exact List.mem_singleton.2 rfl
  obtain ⟨m1, m2⟩ := List.mem_filter.1 m
  exact ⟨List.mem_range.1 m1, of_decide_eq_true m2⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {Bk : ProverCoinCounts} {Wl Xi Y : Type}

/-- THE HEAD, THE OPENING AND hP ARE PREMISES. **The lot of the opening's message 4, at the number
`k4IndexNum Zp`, lies in K1's authors' list at the opening's member.** -/
theorem openingLot_mem (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (front : Nat) (wit : Wl → PlaceIn Xi) (own₀ : Y) (J : SendJob (PlaceIn Xi) Y)
    (hP : J.P = firstPar Bs.G₀.first (gpOf Zp)) :
    (⟨k4IndexNum Zp, front + roundsTo cF.blocksInOrder 2, msgTxt 0 wit J own₀ 4⟩ : MsgLot Bk Wl) ∈
      k1MsgLotsAt cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ (2, J) := by
  have hs : seatAtMember cF.blocksInOrder 2 J.P 4 = (1, 0) := by
    rw [hP, seat_two_written h O 4]
    exact four_is_index.2
  have hn : 4 < J.P.sent.size := by
    rw [hP, par_at_head h O]
    exact four_is_index.1
  unfold k1MsgLotsAt
  refine List.mem_map.2 ⟨4, List.mem_range.2 hn, ?_⟩
  show (⟨P5J.At.arr Zp (seatAtMember cF.blocksInOrder 2 J.P 4).1 (seatAtMember cF.blocksInOrder 2 J.P 4).2,
    front + roundsTo cF.blocksInOrder 2, msgTxt 0 wit J own₀ 4⟩ : MsgLot Bk Wl) = _
  rw [hs]
  rfl

/-- So it lies in the whole list, at every list of jobs that holds the opening's. -/
theorem openingLot_mem_list (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (front : Nat) (wit : Wl → PlaceIn Xi) (own₀ : Y) (J : SendJob (PlaceIn Xi) Y)
    (hP : J.P = firstPar Bs.G₀.first (gpOf Zp))
    (jobs : List (Nat × SendJob (PlaceIn Xi) Y)) (hx : (2, J) ∈ jobs) :
    (⟨k4IndexNum Zp, front + roundsTo cF.blocksInOrder 2, msgTxt 0 wit J own₀ 4⟩ : MsgLot Bk Wl) ∈
      k1MsgLots cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ jobs :=
  mem_k1MsgLots hx (openingLot_mem h O front wit own₀ J hP)

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.four_is_index
#print axioms ProofFile.Honest.K11.openingLot_mem
#print axioms ProofFile.Honest.K11.openingLot_mem_list
