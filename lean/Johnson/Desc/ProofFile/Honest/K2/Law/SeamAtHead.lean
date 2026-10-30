-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SeamAtHead.lean: the kind "the code switch" (K2): THE SEAM
BETWEEN THE TWO SPELLINGS OF A SWITCH's SEATS: `seatK10`
(Johnson/Desc/First/Close/Law/SeatsOfLink.lean), which the closing's laws use, and `seatAtMember`
(Honest/K1/Seated.lean), which the kind's ties at the joined Script use. Public data alone: no coin,
input or run occurs. Four laws and one closed fact by evaluation in Lean's kernel, with a control;
no definition.

  `seam_at_head`    at each message of a switch but the last: the n-th member's `seatK10` is
                    `seatAtMember` at n
  `lastFirstW`, `last_first`   BY LEAN's KERNEL: a switch sends a message and is the first sender of
                    its last; a control
  `mask_num_at_head`   the last message's number is the witness's at the closing's seat
  `seam_mask_at_head`   at the last, the fold's fresh mask: the closing's `maskTree`, `maskPart`

By, ours: `seat_at_head`, `maskSeat_at_head` (Honest/K2/Law/SeatIsK10.lean) · `share_seat`
(Honest/K2/Law/TieAtJoin.lean). Both come to the one seat that `switchSeatIn` returns.

Limits. THE HEAD AND THE OPENING ARE HYPOTHESES: THIS FILE SHOWS THEM MET BY NOTHING: WHERE NOTHING
MEETS THEM THESE LAWS HOLD EMPTILY. A CLOSED FACT BY LEAN's KERNEL, REPLAYED BY NO INDEPENDENT
CHECKER. Numbers and seats alone: nothing on what a seat's message holds. The full size and the
format's second hash function alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SeatIsK10
import Johnson.Desc.ProofFile.Honest.K2.Law.TieAtJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First.Close (seatK10)
open VerifiableInference.Desc.LinkJoin (loAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.K1 (seatAtMember)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block TS ProofFile.Cl)} {p : SwitchPlace}

/-- **At each message but the last the two spellings of the seat are one.** -/
theorem seam_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size - 1) {i : Fin (loAt p.link).length}
    (hi : (VerifiableInference.Desc.First.Close.membersOf (loAt p.link))[n]? = some i) :
    seatK10 (loAt p.link) (P5J.At.pseats Zp) p.link i =
      seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n := by
  obtain ⟨i', q, hi', hq, hs, -⟩ := seat_at_head h.toAtMg O p hp n hn
  obtain rfl : i = i' := Option.some.inj (hi.symm.trans hi')
  obtain ⟨q', hq', e, -⟩ := share_seat h O hp (n := n) (by omega)
  obtain rfl : q = q' := Option.some.inj (hq.symm.trans hq')
  exact hs.trans e

set_option maxRecDepth 1000000 in
/-- **At each written switch the sending has a message, and the switch is the first sender of its
last**; a control: `firstSender` at message 1 fails at some written switch. -/
theorem lastFirstW : (placesW.all fun p => decide (0 < (switchSent p.sizes p.others).size) &&
      firstSender p ((switchSent p.sizes p.others).size - 1)) = true ∧
    (placesW.all fun p => firstSender p 1) = false := by
  decide +kernel

/-- **Under the head: the same at each switch of the plan.** -/
theorem last_first (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) :
    0 < (switchSent p.sizes p.others).size ∧
      firstSender p ((switchSent p.sizes p.others).size - 1) = true := by
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  have a := List.all_eq_true.1 lastFirstW.1 p hpW
  rw [Bool.and_eq_true, decide_eq_true_eq] at a
  exact a

/-- **The last message's number is the witness's number at the closing's seat.** -/
theorem mask_num_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) :
    switchNum Zp p ((switchSent p.sizes p.others).size - 1) =
      P5J.At.arr Zp (VerifiableInference.Desc.First.Close.maskTree p.link)
        (VerifiableInference.Desc.First.Close.maskPart p.link) := by
  obtain ⟨q, -, hs, ha⟩ := maskSeat_at_head h.toAtMg O p hp
  have e1 := congrArg Prod.fst hs
  have e2 := congrArg Prod.snd hs
  simp only at e1 e2
  rw [e1, e2]
  exact ha.symm

/-- **At the last message, the fold's fresh mask, the closing's seat is `seatAtMember`.** -/
theorem seam_mask_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) :
    (VerifiableInference.Desc.First.Close.maskTree p.link,
        VerifiableInference.Desc.First.Close.maskPart p.link) =
      seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) ((switchSent p.sizes p.others).size - 1) := by
  have h0 := (last_first h O hp).1
  obtain ⟨q, hq, hs, -⟩ := maskSeat_at_head h.toAtMg O p hp
  obtain ⟨q', hq', e, -⟩ := share_seat h O hp
    (n := (switchSent p.sizes p.others).size - 1) (by omega)
  obtain rfl : q = q' := Option.some.inj (hq.symm.trans hq')
  exact hs.trans e

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.seam_at_head
#print axioms ProofFile.Honest.K2.Law.lastFirstW
#print axioms ProofFile.Honest.K2.Law.last_first
#print axioms ProofFile.Honest.K2.Law.mask_num_at_head
#print axioms ProofFile.Honest.K2.Law.seam_mask_at_head
