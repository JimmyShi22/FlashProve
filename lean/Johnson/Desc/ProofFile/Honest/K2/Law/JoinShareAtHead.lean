-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/JoinShareAtHead.lean: the kind "the code switch" (K2): NUMBERS
OF A PUBLIC PLAN: THE KIND's SHARE OF THE JOINED LIST (`switchShareAt`, Honest/K2/JoinShare.lean)
UNDER THE HEAD AND THE OPENING: its lots of messages agree among themselves, its lots of pads agree
among themselves, each of them stands far from the shared sending's, and no default of the share is
read. One definition, a list of public numbers; two closed facts by evaluation in Lean's kernel,
each with a control; lemmas.

  `nums_share`, `seats_share`   the public face of a share: its lots' numbers; its pads' seats
  `padSeats`     the tree and tenant at which each message's lot of pads is laid, over a list of
                 places
  `padSeatsW`    BY LEAN's KERNEL: at the 25 written places there are 132, and no two are one; A
                 CONTROL: with the first place laid twice two are one
  `switchSeatsW`, `share_seats_at_head`   BY LEAN's KERNEL, then under the head: the test
                 `switchSeatsB` passes; A CONTROL, A WEAK ONE: at the empty list of seats it says
                 no, for want of a seat: its clause on the tree is not shown to reject
  `share_msgsAgree_at_head`, `share_padsAgree_at_head`   `MsgsAgree` and `PadsAgree` of the share's
                 own two lists
  `share_far_msgs_at_head`, `share_far_pads_at_head`   the ends of Honest/K2/Law/FarAtHead.lean at
                 the share's whole lists

By: `firstNums_at_head`, `places_at_head`, `pseatsAll_at_head`
(Honest/K2/Law/SwitchNumsAtHead.lean, PlacesWritten.lean) · `msgsAgree_of_nodup`,
`padsAgree_of_nodup` (Honest/Thread/Join.lean, of other authors) · `far_msgs_at_head`,
`far_pads_at_head`.

Limits. NUMBERS AND SEATS ALONE: no lot's text is opened; no coin, input or run occurs. That lots
agree is no tie. THE SHARE's OWN LISTS: that they agree with the shared sending's lots is not drawn
here: the last two ends are written after the premises hfar of Honest/K1/Law/AgreeFar.lean (of other
authors; not imported). Of other kinds' lots nothing is said. The full size and the format's second
hash function alone. The head and the opening are premises; that they can be met is not said. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K2.JoinShare
import Johnson.Desc.ProofFile.Honest.K2.Law.FarAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (momL)
open P5T (PSeat Role seatsAllFull)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest.FirstThread (TreeLot MsgsAgree PadsAgree nums seatsOf msgsAgree_of_nodup
  padsAgree_of_nodup)

variable {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- The numbers of a share's lots of messages. -/
theorem nums_share (ch : Nat) (Sd : Sender) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (no fx : SwitchPlace → Nat)
    (num : SwitchPlace → Nat → Nat) (tree : SwitchPlace → Nat) (tenant : SwitchPlace → Nat → Nat)
    (places : List SwitchPlace) (rest : Nat → TreeLot Bk (Local W₀ Rc Xi Tr)) :
    nums (switchShare Bk ch Sd D readers closing no fx num tree tenant places rest).ml =
      firstNums num places := by
  show (places.flatMap fun p => switchMsgLots ch D readers closing p (num p) (fx p)).map (·.n) = _
  unfold firstNums
  rw [List.map_flatMap]
  refine List.flatMap_congr fun p _ => ?_
  unfold switchMsgLots
  rw [List.map_map]
  rfl

/-- The seats of a share's lots of pads. -/
theorem seats_share (ch : Nat) (Sd : Sender) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (no fx : SwitchPlace → Nat)
    (num : SwitchPlace → Nat → Nat) (tree : SwitchPlace → Nat) (tenant : SwitchPlace → Nat → Nat)
    (places : List SwitchPlace) (rest : Nat → TreeLot Bk (Local W₀ Rc Xi Tr)) :
    seatsOf (switchShare Bk ch Sd D readers closing no fx num tree tenant places rest).pl =
      places.flatMap fun p =>
        (List.range (switchSent p.sizes p.others).size).map fun n => (tree p, tenant p n) := by
  show (places.flatMap fun p => switchPadLots ch p (tree p) (tenant p)).map
    (fun L => (L.j, L.t)) = _
  rw [List.map_flatMap]
  refine List.flatMap_congr fun p _ => ?_
  unfold switchPadLots
  rw [List.map_map]
  rfl

/-- The tree and tenant at which each message's lot of pads is laid, over a list of places. -/
def padSeats (ps : List PSeat) (l : List SwitchPlace) : List (Nat × Nat) :=
  l.flatMap fun p => (List.range (switchSent p.sizes p.others).size).map fun n =>
    (((switchSeatIn ps p.link 0).map (·.j)).getD 0, ((switchSeatIn ps p.link n).map (·.t)).getD 0)

set_option maxRecDepth 1000000 in
/-- **At the written lists: 132 seats, no two one**; a control that says no. -/
theorem padSeatsW :
    (padSeats seatsAllFull placesW).length = 132 ∧ (padSeats seatsAllFull placesW).Nodup ∧
      ¬ (padSeats seatsAllFull (placesW ++ placesW.take 1)).Nodup := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **At the written lists the test on the seats passes**; a control that says no. -/
theorem switchSeatsW :
    switchSeatsB seatsAllFull placesW = true ∧ switchSeatsB [] (placesW.take 1) = false := by
  decide +kernel

variable {W : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **UNDER THE HEAD AND THE OPENING: THE TEST ON THE SEATS PASSES**: no default of the share is
read. -/
theorem share_seats_at_head (h : AtMg OnBytes.secondHashFunction W D₀ r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    switchSeatsB (P5J.At.pseatsAll Zp) (switchPlaces Zp Bs.G₀) = true := by
  rw [places_at_head h O, pseatsAll_at_head h]
  exact switchSeatsW.1

/-- **UNDER THE HEAD AND THE OPENING: THE SHARE's LOTS OF MESSAGES AGREE AMONG THEMSELVES.** -/
theorem share_msgsAgree_at_head (h : AtMg OnBytes.secondHashFunction W D₀ r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (bs : List (Block S ProofFile.Cl)) (front : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (rest : Nat → TreeLot Bk (Local W₀ Rc Xi Tr)) :
    MsgsAgree (switchShareAt Bk bs front Zp Bs.G₀ D readers rest).ml := by
  refine msgsAgree_of_nodup ?_
  unfold switchShareAt
  rw [nums_share]
  exact firstNums_at_head h O

/-- **UNDER THE HEAD AND THE OPENING: THE SHARE's LOTS OF PADS AGREE AMONG THEMSELVES.** -/
theorem share_padsAgree_at_head (h : AtMg OnBytes.secondHashFunction W D₀ r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (bs : List (Block S ProofFile.Cl)) (front : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (rest : Nat → TreeLot Bk (Local W₀ Rc Xi Tr)) :
    PadsAgree (switchShareAt Bk bs front Zp Bs.G₀ D readers rest).pl := by
  refine padsAgree_of_nodup ?_
  unfold switchShareAt
  rw [seats_share, places_at_head h O, pseatsAll_at_head h]
  exact padSeatsW.2.1

/-- **UNDER THE HEAD AND THE OPENING: EACH LOT OF MESSAGES OF THE SHARE STANDS FAR.** -/
theorem share_far_msgs_at_head (h : AtMg OnBytes.secondHashFunction W D₀ r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (bs : List (Block S ProofFile.Cl)) (front : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (rest : Nat → TreeLot Bk (Local W₀ Rc Xi Tr)) :
    ∀ L' ∈ (switchShareAt Bk bs front Zp Bs.G₀ D readers rest).ml, ∃ j t q,
      ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q ∧
        L'.n = P5J.At.arr Zp j t ∧ (∀ l' k', q.role ≠ .kept l' k') ∧ q.send ≠ 0 ∧
        (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81 := by
  intro L' hL'
  obtain ⟨p, hp, hL⟩ := List.mem_flatMap.1 hL'
  exact far_msgs_at_head h O 0 D readers _ _ p hp L' hL

/-- **UNDER THE HEAD AND THE OPENING: EACH LOT OF PADS OF THE SHARE STANDS FAR.** -/
theorem share_far_pads_at_head (h : AtMg OnBytes.secondHashFunction W D₀ r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (bs : List (Block S ProofFile.Cl)) (front : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (rest : Nat → TreeLot Bk (Local W₀ Rc Xi Tr)) :
    ∀ L' ∈ (switchShareAt Bk bs front Zp Bs.G₀ D readers rest).pl,
      ∃ q ∈ P5J.At.pseatsAll Zp, L'.j = q.j ∧ L'.t = q.t ∧ q.send ≠ 0 ∧
        (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81 := by
  intro L' hL'
  obtain ⟨p, hp, hL⟩ := List.mem_flatMap.1 hL'
  exact far_pads_at_head h O 0 p hp L' hL

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.nums_share
#print axioms ProofFile.Honest.K2.Law.seats_share
#print axioms ProofFile.Honest.K2.Law.padSeats
#print axioms ProofFile.Honest.K2.Law.padSeatsW
#print axioms ProofFile.Honest.K2.Law.switchSeatsW
#print axioms ProofFile.Honest.K2.Law.share_seats_at_head
#print axioms ProofFile.Honest.K2.Law.share_msgsAgree_at_head
#print axioms ProofFile.Honest.K2.Law.share_padsAgree_at_head
#print axioms ProofFile.Honest.K2.Law.share_far_msgs_at_head
#print axioms ProofFile.Honest.K2.Law.share_far_pads_at_head
