-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/XchSeatsAt.lean: the closing of a segment (K10): two clauses of the field stand of
`TieBySwitch` (Pay/XchTieBySwitch.lean) and the count of the group's members that `tie_of_range` (Pay/XchTieRange.lean) asks,
under the head, at a reached state in front of the closing of a segment into which a code switch leads.

  `seatSw`            the seat of the switch's message number n, off the public part's list of all seats: the term at which the laws
                    on the first chain's script speak (`switchSeatIn`, Honest/K2/SwitchNums.lean)
  `at_of_idx`         a number's place in an array, as a member of the array's list
  **`switch_seats_at`**   the group's member at the place n of the group's list has that seat in the state's book, and the shape of the
                    switch's message number n
  **`switch_count_at`**   the group has as many members as the switch's sending has messages, and one more

By: `member_at_closing`, `members_at_closing` (Pay/SeatsAtStand.lean); `seat_at_switch`, `count_at_switch` (Pay/XchSeats.lean);
`AtMg.seats_written` (Johnson/HB/LLHARD/MaskSeatWritten.lean).

Limits. The head is a premise; that the state is reached, has not failed and has the group is a premise. The full size and the
older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.SeatsAtStand
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchSeats
import Johnson.HB.LLHARD.MaskSeatWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc
open VerifiableInference.Desc.Sound (seatBy noFirst)
open Johnson.Desc.First.Walk.Tied (Reach)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest.K2 (SwitchPlace switchSent switchSeatIn)
open ProofFile.Honest.K2.Law (placesW)

/-- The seat of the switch's message number n, off the public part's list of all seats; (0, 0) where there is none. -/
def seatSw (Zp : ProofFile.Pub) (p : SwitchPlace) (n : Nat) : Nat × Nat :=
  ((switchSeatIn (P5J.At.pseatsAll Zp) p.link n).map fun q => (q.j, q.t)).getD (0, 0)

/-- A number's place in an array, as a member of the array's list. -/
theorem at_of_idx {A : Array Nat} {o i : Nat} (h : A.idxOf? o = some i) : A.toList[i]? = some o := by
  obtain ⟨hlt, hget⟩ := OnBytes.Means.find_some (L := { (default : OnBytes.GroupLayout) with members := A }) h
  have hlt' : i < A.size := hlt
  have hget' : A.getD i OnBytes.noId = o := hget
  rw [Array.getElem?_toList, ← hget', Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hlt']
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The group's first members have the switch's messages' seats and shapes.** -/
theorem switch_seats_at (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {l : Nat} (h1 : 1 ≤ l) (hl : l < 25)
    {p : SwitchPlace} (hp : placesW.find? (·.link == l) = some p) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none)
    {G : OnBytes.Group} (hG : (K9.recOf s).st.groups[(K9.recOf s).frame.group]? = some G) :
    ∀ n, n + 1 < (switchSent p.sizes p.others).size → ∀ o, G.members.idxOf? o = some (0 + n) →
      seatBy noFirst s.book o = some (seatSw Zp p n) ∧
        ∃ y, s.st.oracles[o]? = some y ∧ y.shape = ((switchSent p.sizes p.others).getD n default).shape := by
  intro n hn o ho
  rw [Nat.zero_add] at ho
  obtain ⟨i, hi, -, hseat, y, hy, hsh⟩ := member_at_closing h hl hr hf hG (at_of_idx ho)
  obtain ⟨i', q, hi', hq, e1, e2⟩ := seat_at_switch h1 hl hp hn
  obtain rfl : i = i' := Option.some.inj (hi.symm.trans hi')
  have hlink : p.link = l := by
    have := List.find?_some hp
    exact eq_of_beq this
  have w1 : P5J.At.pseats Zp = P5T.psFull := (P5J.AtMg.seats_written h.toAtMg).1
  have w2 : P5J.At.pseatsAll Zp = P5T.seatsAllFull := (P5J.AtMg.seats_written h.toAtMg).2.1
  refine ⟨?_, y, hy, hsh.trans e2⟩
  rw [hseat, w1, e1]
  unfold seatSw
  rw [w2, hlink, hq]
  rfl

/-- **The group has as many members as the switch's sending has messages, and one more.** -/
theorem switch_count_at (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {l : Nat} (h1 : 1 ≤ l) (hl : l < 25)
    {p : SwitchPlace} (hp : placesW.find? (·.link == l) = some p) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) (14 * l + IM.nAt l + 5) (z, s)) (hf : s.failed = none)
    {G : OnBytes.Group} (hG : (K9.recOf s).st.groups[(K9.recOf s).frame.group]? = some G) :
    G.members.size ≤ (switchSent p.sizes p.others).size - 1 + 1 + 1 := by
  have hm := (members_at_closing h hl hr hf hG).1
  have e := congrArg List.length hm
  rw [Array.length_toList, List.length_map, count_at_switch h1 hl hp] at e
  exact Nat.le_of_eq e

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.seatSw
#print axioms ProofFile.Honest.K10.at_of_idx
#print axioms ProofFile.Honest.K10.switch_seats_at
#print axioms ProofFile.Honest.K10.switch_count_at
