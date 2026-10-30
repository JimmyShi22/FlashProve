-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SeatIsK10.lean: TWO WAYS TO FIND THE SEAT OF A MESSAGE OF A
SWITCH's SENDING GIVE ONE SEAT. `switchSeatIn` (Honest/K2/SwitchNums.lean) finds it in the list of
ALL THREE CHAINS' seats by the segment (l, 0) and the message's number n. The closing's `seatK10`
(Johnson/Desc/First/Close/Law/SeatsOfLink.lean) finds it in the FIRST CHAIN's list by a member's
number among the link's sampled seats. AT EVERY MESSAGE BUT THE LAST the n-th member of the link's
written list has the seat of message n; THE LAST MESSAGE, the fold's fresh mask, is no member: its
seat is the closing's `maskSeat` (MaskAtFull.lean there). PUBLIC DATA ALONE: written lists of places
and seats. Three definitions: two public tests and a helper. Lemmas; none of the library's goals.

  `seatTie` psAll ps l n  A PUBLIC TEST: the list `membersOf (loAt l)` has an n-th member i,
                          `switchSeatIn` psAll l n returns a seat q, and the link's sampled seats in
                          ps have at the number i JUST (q.j, q.t): asked by `[i]?`, so that no
                          default can say yes
  `maskTie` psAll ps l n  A PUBLIC TEST: `maskEntry` ps l and `switchSeatIn` psAll l n both return,
                          with one seat
  `butLast` p f           f holds at every n below the number of p's messages less one
  `seatTieW`, `maskTieW`  both accept at each place of the written list `placesW`, at the two
                          written lists of seats: the first at all messages but the last, the second
                          at the last: BY LEAN's KERNEL
  `seatTieW_last`, `seatTieW_next`, `maskTieW_first`
                          CONTROLS THAT SAY NO: `seatTie` at the last message, at every written
                          place; `seatTie` at the next link's lists; `maskTie` at message 0
  `seatTie_gives`, `maskTie_gives`
                          what a yes says, as equations; with `seatK10` and `maskSeat` themselves
  `seat_at_head`          UNDER THE HEAD AND THE OPENING, at each place p of `switchPlaces` Zp Bs.G₀
                          and each n below the sending's size less one: there are i and q: the n-th
                          member is i; `switchSeatIn` at the public part's list returns q; `seatK10`
                          (loAt p.link) (At.pseats Zp) p.link i = (q.j, q.t); At.arr Zp q.j q.t =
                          `switchNum` Zp p n
  `maskSeat_at_head`      there, at the last message: `switchSeatIn` returns a q with (maskTree
                          p.link, maskPart p.link) = (q.j, q.t), and At.arr Zp q.j q.t = `switchNum`
                          Zp p n

TWO LISTS. At.pseatsAll Zp holds the seats of all three chains, At.pseats Zp those of the first
(Johnson/P5J/LettersAt.lean): the tests keep them apart as two letters; the closed facts speak of
both written lists, `P5T.seatsAllFull` and `P5T.psFull`.

WHAT IT IS NOT. The last conjunct on At.arr is `switchNumIn`'s own text at the seat that
`switchSeatIn` returns: it adds no tie. That a lot of messages or of pads is laid at these seats is
not said. Nothing on what a seat's message holds. That the hypothesis on the public files can be met
is not said.

Limits. FIVE CLOSED FACTS BY EVALUATION IN LEAN's KERNEL. The full size and the format's second
hash function alone. The head and the opening are premises. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchNumsAtHead
import Johnson.IMR.K10SeatFit
import Johnson.Desc.First.Close.Law.Drawn.Def
import Johnson.Desc.First.Close.Law.SeatsOfLink
import Johnson.Desc.First.Close.Law.MaskLaidFull
import Johnson.LPFE1R.RowPubAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open P5T (PSeat seatsAllFull psFull)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **A PUBLIC TEST**: the n-th member's seat among the link's sampled seats is message n's. -/
def seatTie (psAll ps : List PSeat) (l n : Nat) : Bool :=
  match (VerifiableInference.Desc.First.Close.membersOf
      (VerifiableInference.Desc.LinkJoin.loAt l))[n]?, switchSeatIn psAll l n with
  | some i, some q =>
    (VerifiableInference.Desc.First.Close.seatsOfLink ps l)[i.val]? == some (q.j, q.t)
  | _, _ => false

/-- **A PUBLIC TEST**: the closing's entry of the fresh mask has message n's seat. -/
def maskTie (psAll ps : List PSeat) (l n : Nat) : Bool :=
  match VerifiableInference.Desc.First.Close.maskEntry ps l, switchSeatIn psAll l n with
  | some e, some q => e.seat == (q.j, q.t)
  | _, _ => false

/-- A test holds at every message of the place's sending but the last. -/
def butLast (p : SwitchPlace) (f : Nat → Bool) : Bool :=
  (List.range ((switchSent p.sizes p.others).size - 1)).all f

set_option maxRecDepth 1000000 in
/-- **At the written lists: every message but the last.** -/
theorem seatTieW :
    (placesW.all fun p => butLast p (seatTie seatsAllFull psFull p.link)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **At the written lists: the last message.** -/
theorem maskTieW :
    (placesW.all fun p =>
      maskTie seatsAllFull psFull p.link ((switchSent p.sizes p.others).size - 1)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at the last message `seatTie` says no, at every written place. -/
theorem seatTieW_last :
    (placesW.any fun p =>
      seatTie seatsAllFull psFull p.link ((switchSent p.sizes p.others).size - 1)) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at the next link's lists `seatTie` does not hold throughout. -/
theorem seatTieW_next :
    (placesW.all fun p => butLast p (seatTie seatsAllFull psFull (p.link + 1))) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at message 0 `maskTie` says no, at every written place. -/
theorem maskTieW_first :
    (placesW.any fun p => maskTie seatsAllFull psFull p.link 0) = false := by
  decide +kernel

/-- What the first test's yes says. -/
theorem seatTie_gives {psAll ps : List PSeat} {l n : Nat} (h : seatTie psAll ps l n = true) :
    ∃ i q, (VerifiableInference.Desc.First.Close.membersOf
        (VerifiableInference.Desc.LinkJoin.loAt l))[n]? = some i ∧
      switchSeatIn psAll l n = some q ∧
      (VerifiableInference.Desc.First.Close.seatsOfLink ps l)[i.val]? = some (q.j, q.t) ∧
      VerifiableInference.Desc.First.Close.seatK10 (VerifiableInference.Desc.LinkJoin.loAt l) ps l
        i = (q.j, q.t) := by
  unfold seatTie at h
  split at h
  · rename_i i q hi hq
    have e := beq_iff_eq.1 h
    refine ⟨i, q, hi, hq, e, ?_⟩
    unfold VerifiableInference.Desc.First.Close.seatK10
    rw [List.getD_eq_getElem?_getD, e]
    rfl
  · exact nomatch h

/-- What the second test's yes says. -/
theorem maskTie_gives {psAll ps : List PSeat} {l n : Nat} (h : maskTie psAll ps l n = true) :
    ∃ q, switchSeatIn psAll l n = some q ∧
      VerifiableInference.Desc.First.Close.maskSeat ps l = (q.j, q.t) := by
  unfold maskTie at h
  split at h
  · rename_i e q he hq
    refine ⟨q, hq, ?_⟩
    unfold VerifiableInference.Desc.First.Close.maskSeat
    rw [he]
    exact beq_iff_eq.1 h
  · exact nomatch h

/-- The number at the seat that `switchSeatIn` returns: `switchNumIn`'s own text. -/
theorem switchNumIn_at {ps : List PSeat} {l n : Nat} {q : PSeat}
    (h : switchSeatIn ps l n = some q) : P5T.arrOf ps q.j q.t = switchNumIn ps l n := by
  unfold switchNumIn
  rw [h]

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **Under the head and the opening: every message but the last.** -/
theorem seat_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, ∀ n, n < (switchSent p.sizes p.others).size - 1 →
      ∃ i q, (VerifiableInference.Desc.First.Close.membersOf
          (VerifiableInference.Desc.LinkJoin.loAt p.link))[n]? = some i ∧
        switchSeatIn (P5J.At.pseatsAll Zp) p.link n = some q ∧
        VerifiableInference.Desc.First.Close.seatK10
          (VerifiableInference.Desc.LinkJoin.loAt p.link) (P5J.At.pseats Zp) p.link i =
            (q.j, q.t) ∧
        P5J.At.arr Zp q.j q.t = switchNum Zp p n := by
  rw [places_at_head h O]
  intro p hp n hn
  have hs : P5J.At.pseats Zp = psFull := h.seats
  obtain ⟨i, q, hi, hq, _, hk⟩ := seatTie_gives
    (List.all_eq_true.1 (List.all_eq_true.1 seatTieW p hp) n (List.mem_range.2 hn))
  rw [pseatsAll_at_head h, hs]
  refine ⟨i, q, hi, hq, hk, ?_⟩
  show P5T.arrOf (P5J.At.pseatsAll Zp) q.j q.t = switchNumIn (P5J.At.pseatsAll Zp) p.link n
  rw [pseatsAll_at_head h]
  exact switchNumIn_at hq

/-- **Under the head and the opening: the last message, the fold's fresh mask.** -/
theorem maskSeat_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀,
      ∃ q, switchSeatIn (P5J.At.pseatsAll Zp) p.link ((switchSent p.sizes p.others).size - 1) =
          some q ∧
        (VerifiableInference.Desc.First.Close.maskTree p.link,
          VerifiableInference.Desc.First.Close.maskPart p.link) = (q.j, q.t) ∧
        P5J.At.arr Zp q.j q.t = switchNum Zp p ((switchSent p.sizes p.others).size - 1) := by
  rw [places_at_head h O]
  intro p hp
  obtain ⟨q, hq, hm⟩ := maskTie_gives (List.all_eq_true.1 maskTieW p hp)
  rw [pseatsAll_at_head h]
  refine ⟨q, hq, hm, ?_⟩
  show P5T.arrOf (P5J.At.pseatsAll Zp) q.j q.t =
    switchNumIn (P5J.At.pseatsAll Zp) p.link ((switchSent p.sizes p.others).size - 1)
  rw [pseatsAll_at_head h]
  exact switchNumIn_at hq

end ProofFile.Honest.K2.Law

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.Law.seatTie
#print axioms ProofFile.Honest.K2.Law.maskTie
#print axioms ProofFile.Honest.K2.Law.butLast
#print axioms ProofFile.Honest.K2.Law.seatTieW
#print axioms ProofFile.Honest.K2.Law.maskTieW
#print axioms ProofFile.Honest.K2.Law.seatTieW_last
#print axioms ProofFile.Honest.K2.Law.seatTieW_next
#print axioms ProofFile.Honest.K2.Law.maskTieW_first
#print axioms ProofFile.Honest.K2.Law.seatTie_gives
#print axioms ProofFile.Honest.K2.Law.maskTie_gives
#print axioms ProofFile.Honest.K2.Law.switchNumIn_at
#print axioms ProofFile.Honest.K2.Law.seat_at_head
#print axioms ProofFile.Honest.K2.Law.maskSeat_at_head
