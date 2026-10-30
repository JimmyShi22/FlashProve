-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/SwitchNumsAtHead.lean: UNDER THE LIBRARY's HEAD AND THE
OPENING: AT EACH PLACE OF THE LIST `switchPlaces`: THE PUBLIC TEST `numsApart` ACCEPTS AT THE
NUMBERS `switchNum` (Honest/K2/SwitchNums.lean); THE NUMBERS OF ALL FIRST SENDERS OF ALL PLACES OF
THE LIST ARE DIFFERENT; AT A SEAT WHOSE ROLE IS "own k" THE NUMBER IS `P5J.At.num` Zp p.link k. No
definition. Lemmas; none of the library's goals. In the form of PublicAtHead.lean of this folder.

  `pseatsAll_at_head`     the public part's list of seats is the written one
  `switchNum_at_head`     so `switchNum` Zp is `switchNumIn` at the written list
  `seatOnce_at_head`      a seat, and just one, at every n below the number of the place's messages
  `firstHolds_at_head`    the first holder of its tree and tenant has the seat's own key
  `firstNotKept_at_head`  first sender: just where the seat's role is no kept copy's
  `numsApart_at_head`     **`numsApart` p (`switchNum` Zp p) = true**
  `firstNums_at_head`     **the first senders' numbers are different across the places of the list
                          too**
  `ownNumOk_gives`        a tool: what the test `ownNumOk` gives at a seat whose role is "own k"
  `ownNum_at_head`        **at a seat whose role is "own k": `switchNum` Zp p n = `P5J.At.num` Zp
                          p.link k**
  `ownBack_at_head`       the way back, as a test's yes: each message of moment 0 of link p.link of
                          the public part's shape is the role of a first sender's seat

How. `places_at_head` (PlacesWritten.lean of this folder), `AtMg.seats_written` and
`AtMg.shape_written` (Johnson/HB/LLHARD/MaskSeatWritten.lean) bring the lists to the written ones;
there the closed facts of SwitchNumsWritten.lean of this folder.

WHAT IT IS NOT. Facts on the plan's own lists: no state, no run, no input; no lot of messages is
laid. That the tree and tenant under which the switch's own tables lie are the seat's is not said
here. `ownBack_at_head` is left as the test's yes: it is not unfolded into "there is an n". The
number of the list's places is 25 by `places_at_head` and `placesW_count` (PlacesCount.lean of this
folder). That the head can be met is not said here.

Limits. Rewritings over closed facts. The written lists are the full size's; the head is taken at
the format's second hash function. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchNumsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open P5T (Role seatsAllFull)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- The public part's list of seats is the written one. -/
theorem pseatsAll_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF) :
    P5J.At.pseatsAll Zp = seatsAllFull :=
  (P5J.AtMg.seats_written h).2.1

/-- So the numbers are those at the written list. -/
theorem switchNum_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF) :
    switchNum Zp = fun p n => switchNumIn seatsAllFull p.link n := by
  funext p n
  unfold switchNum
  rw [pseatsAll_at_head h]

/-- A seat, and just one, at every number of a message of the place. -/
theorem seatOnce_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, ∀ n, n < (switchSent p.sizes p.others).size →
      seatOnce (P5J.At.pseatsAll Zp) p.link n = true := by
  rw [places_at_head h O, pseatsAll_at_head h]
  intro p hp n hn
  exact List.all_eq_true.1 (List.all_eq_true.1 seatOnceW p hp) n (List.mem_range.2 hn)

/-- The first holder of the seat's tree and tenant has the seat's own key. -/
theorem firstHolds_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, ∀ n, n < (switchSent p.sizes p.others).size →
      firstHolds (P5J.At.pseatsAll Zp) p.link n = true := by
  rw [places_at_head h O, pseatsAll_at_head h]
  intro p hp n hn
  exact List.all_eq_true.1 (List.all_eq_true.1 firstHoldsW p hp) n (List.mem_range.2 hn)

/-- A first sender: just where the seat's role is no kept copy's. -/
theorem firstNotKept_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, ∀ n, n < (switchSent p.sizes p.others).size →
      firstNotKept (P5J.At.pseatsAll Zp) p n = true := by
  rw [places_at_head h O, pseatsAll_at_head h]
  intro p hp n hn
  exact List.all_eq_true.1 (List.all_eq_true.1 firstNotKeptW p hp) n (List.mem_range.2 hn)

/-- **The test accepts at each place of the kind's list.** -/
theorem numsApart_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, numsApart p (switchNum Zp p) = true := by
  rw [places_at_head h O, switchNum_at_head h]
  exact List.all_eq_true.1 numsApartW

/-- **Across the places of the list too.** -/
theorem firstNums_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    (firstNums (switchNum Zp) (switchPlaces Zp Bs.G₀)).Nodup := by
  rw [places_at_head h O, switchNum_at_head h]
  exact firstNumsW.2

/-- What the test `ownNumOk` gives. -/
theorem ownNumOk_gives {ps : List P5T.PSeat} {l n k : Nat} (h : ownNumOk ps l n = true)
    (hr : (switchSeatIn ps l n).map (·.role) = some (Role.own k)) :
    switchNumIn ps l n = P5T.numOfPlan ps l k := by
  unfold ownNumOk at h
  rw [hr] at h
  exact beq_iff_eq.1 h

/-- **At an own message the number is the plan's number of the link's message.** -/
theorem ownNum_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, ∀ n k, n < (switchSent p.sizes p.others).size →
      (switchSeatIn (P5J.At.pseatsAll Zp) p.link n).map (·.role) = some (Role.own k) →
      switchNum Zp p n = P5J.At.num Zp p.link k := by
  rw [places_at_head h O]
  intro p hp n k hn hr
  show switchNumIn (P5J.At.pseatsAll Zp) p.link n = P5T.numOfPlan (P5J.At.pseatsAll Zp) p.link k
  refine ownNumOk_gives ?_ hr
  rw [pseatsAll_at_head h]
  exact List.all_eq_true.1 (List.all_eq_true.1 ownNumW p hp) n (List.mem_range.2 hn)

/-- The way back, as the test's yes. -/
theorem ownBack_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, ownBack Zp.first.shape (P5J.At.pseatsAll Zp) p = true := by
  rw [places_at_head h O, pseatsAll_at_head h, P5J.AtMg.shape_written h]
  exact List.all_eq_true.1 ownBackW

end ProofFile.Honest.K2.Law

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.Law.pseatsAll_at_head
#print axioms ProofFile.Honest.K2.Law.switchNum_at_head
#print axioms ProofFile.Honest.K2.Law.seatOnce_at_head
#print axioms ProofFile.Honest.K2.Law.firstHolds_at_head
#print axioms ProofFile.Honest.K2.Law.firstNotKept_at_head
#print axioms ProofFile.Honest.K2.Law.numsApart_at_head
#print axioms ProofFile.Honest.K2.Law.firstNums_at_head
#print axioms ProofFile.Honest.K2.Law.ownNumOk_gives
#print axioms ProofFile.Honest.K2.Law.ownNum_at_head
#print axioms ProofFile.Honest.K2.Law.ownBack_at_head
