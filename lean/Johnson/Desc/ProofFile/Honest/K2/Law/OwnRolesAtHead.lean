-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/OwnRolesAtHead.lean: UNDER THE LIBRARY's HEAD AND THE OPENING:
AT EVERY SWITCH OF THE PLAN, THE SEAT OF EACH OWN MESSAGE OF THE NEXT SEGMENT THAT THE SWITCH SENDS
HAS THE ROLE own m, m THAT MESSAGE's NUMBER AMONG THESE; SO THE NUMBER THAT THE SWITCH's LOTS BEAR
FOR IT IS THE LINK's OWN MESSAGE's NUMBER. By the writers of the merge of the claims on the weights
(sub-protocol K11), on an ask of the authors of K5's honest side. PUBLIC DATA ALONE. One definition:
a public test. Lemmas; none of the library's goals.

  `ownRoles` ps p
      A PUBLIC TEST: for each m below the count of the own messages (`p.others` but its last, the
      next fold's fresh mask): message 1 + kept + m is a message of the sending, and its seat
      among ps (`switchSeatIn`) has the role own m
  `ownRolesW`, `ownRolesW_shifted`, `ownCountW`
      BY LEAN's KERNEL, at the written places and the written seats: the test says yes at all 25 ·
      a control: with own (m + 1) in place of own m no message of any place passes · there are 46
      such messages: so the first is not idle
  `ownRole_at_head`
      the role, at the head's own seats (`P5J.At.pseatsAll Zp`), at every p of the plan and every
      such m
  `ownNums_at_head`
      so `switchNum Zp p (1 + p.sizes.kept.length + m) = P5J.At.num Zp p.link m`: by
      `ownNum_at_head` (SwitchNumsAtHead.lean of this folder)

NEAR, ours: `oddRoleW`, `num3_at_head` (Own0AtOddLinks.lean of this folder): the same at message 3
of the twelve odd links below 24, where kept = 2 and m = 0: a case of this file's. `ownBack_at_head`
(SwitchNumsAtHead.lean): each message of moment 0 of a link is the role of some first sender's seat:
not of which number.

WHAT IT IS NOT. That the switch is the FIRST sender of each of these messages is not said here. Of
the kept copies' and the carrying message's seats nothing is said. A statement on a public plan:
nothing on a prover, a coin or a run.

Limits. THREE CLOSED FACTS BY EVALUATION IN LEAN's KERNEL, one of them a control. The full size; the
format's second hash function; the head and the opening are premises. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchNumsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open P5T (PSeat Role seatsAllFull)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **A PUBLIC TEST**: each own message of the next segment that the switch sends is a message of
the sending, and its seat has the role own m. -/
def ownRoles (ps : List PSeat) (p : SwitchPlace) : Bool :=
  (List.range (p.others.size - 1)).all fun m =>
    decide (1 + p.sizes.kept.length + m < (switchSent p.sizes p.others).size) &&
      (switchSeatIn ps p.link (1 + p.sizes.kept.length + m)).map (·.role) == some (Role.own m)

set_option maxRecDepth 1000000 in
/-- **At the written places and seats.** -/
theorem ownRolesW : (placesW.all (ownRoles seatsAllFull)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with own (m + 1) in place of own m no message of any place passes. -/
theorem ownRolesW_shifted :
    (placesW.any fun p => (List.range (p.others.size - 1)).any fun m =>
      (switchSeatIn seatsAllFull p.link (1 + p.sizes.kept.length + m)).map (·.role) ==
        some (Role.own (m + 1))) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- There are 46 such messages: so `ownRolesW` is not idle. -/
theorem ownCountW : (placesW.map fun p => p.others.size - 1).foldl (· + ·) 0 = 46 := by
  decide +kernel

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **The seat's role at every own message of a switch.** -/
theorem ownRole_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, ∀ m, m < p.others.size - 1 →
      1 + p.sizes.kept.length + m < (switchSent p.sizes p.others).size ∧
        (switchSeatIn (P5J.At.pseatsAll Zp) p.link (1 + p.sizes.kept.length + m)).map (·.role) =
          some (Role.own m) := by
  intro p hp m hm
  have hp' : p ∈ placesW := by
    rw [← places_at_head h O]
    exact hp
  have t0 : ((List.range (p.others.size - 1)).all fun m =>
      decide (1 + p.sizes.kept.length + m < (switchSent p.sizes p.others).size) &&
        (switchSeatIn seatsAllFull p.link (1 + p.sizes.kept.length + m)).map (·.role) ==
          some (Role.own m)) = true := List.all_eq_true.1 ownRolesW p hp'
  obtain ⟨t1, t2⟩ := Bool.and_eq_true_iff.1 (List.all_eq_true.1 t0 m (List.mem_range.2 hm))
  rw [pseatsAll_at_head h]
  exact ⟨of_decide_eq_true t1, beq_iff_eq.1 t2⟩

/-- **The number that the switch's lots bear for an own message is the link's own message's.** -/
theorem ownNums_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, ∀ m, m < p.others.size - 1 →
      switchNum Zp p (1 + p.sizes.kept.length + m) = P5J.At.num Zp p.link m := by
  intro p hp m hm
  obtain ⟨a, b⟩ := ownRole_at_head h O p hp m hm
  exact ownNum_at_head h O p hp _ m a b

end ProofFile.Honest.K2.Law

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.Law.ownRoles
#print axioms ProofFile.Honest.K2.Law.ownRolesW
#print axioms ProofFile.Honest.K2.Law.ownRolesW_shifted
#print axioms ProofFile.Honest.K2.Law.ownCountW
#print axioms ProofFile.Honest.K2.Law.ownRole_at_head
#print axioms ProofFile.Honest.K2.Law.ownNums_at_head
