-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/Own0AtOddLinks.lean: THE SWITCH INTO A LINK WITH AN ODD NUMBER
BELOW 24: ITS MESSAGE NUMBER 3 IS THE LINK's OWN MESSAGE 0: IT BEARS THE PLAN's NUMBER OF (the link,
0). PUBLIC DATA ALONE: written lists of places and seats. Two definitions, public tests. Lemmas;
none of the library's goals.

  `oddRole` ps g          A PUBLIC TEST: in ps the seat of message 3 of the sending "link 2 g + 1,
                          moment 0" has the role own 0
  `oddSize` k p           A PUBLIC TEST: a place whose link is odd and below 24 announces k
                          messages; AT ANOTHER PLACE IT SAYS YES AND ASKS NOTHING
  `oddRoleW`, `oddSizeW`  the first accepts at each g below 12 at the written seats, the second, at
                          k := 5, at each written place: BY LEAN's KERNEL
  CONTROLS                `oddRoleW_two`, `oddRoleW_even`: at message 2 of these sendings, and at
                          message 3 of the sendings into the even links 2 g + 2, no seat has the
                          role own 0; `oddSizeW_six`: at k := 6 the test says no; `oddSizeW_bites`:
                          twelve written places have such a link
  `num3_at_head`          UNDER THE HEAD AND THE OPENING, at each place p of `switchPlaces` Zp Bs.G₀
                          with p.link = 2 g + 1, g below 12: `switchNum` Zp p 3 = P5J.At.num Zp (2 g
                          + 1) 0

By. `ownNum_at_head`, `pseatsAll_at_head` (SwitchNumsAtHead.lean of this folder); `places_at_head`
(PlacesWritten.lean). The like at link 24, message 2: `num24_at_head` (Link24Written.lean). NEAR,
another group of authors': `switches_written`, `switch_numbers_head`
(Honest/K5/Law/MaskRowWritten.lean; this library may not hold it): at the same twelve places: five
messages, and message 3 has one mask row: `oddSizeW` IS A FURTHER TEXT OF ONE CLAUSE OF THEIR CLOSED
FACT; the role is not said there.

WHAT IT IS NOT. That another kind's own name of that message is this number is not said: that kind's
authors have their number as At.num at a message number under "there is". No lot is laid. Nothing on
what the message holds. That the hypothesis on the public files can be met is not said.

Limits. SIX CLOSED FACTS BY EVALUATION IN LEAN's KERNEL. The full size and the format's second hash function
alone. The head and the opening are premises. Nothing on any property.
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

/-- **A PUBLIC TEST**: message 3 of the sending into link 2 g + 1 has the role own 0. -/
def oddRole (ps : List PSeat) (g : Nat) : Bool :=
  (switchSeatIn ps (2 * g + 1) 3).map (·.role) == some (Role.own 0)

/-- **A PUBLIC TEST**: k messages at a place with an odd link below 24; nothing at another. -/
def oddSize (k : Nat) (p : SwitchPlace) : Bool :=
  decide (p.link % 2 = 1 → p.link < 24 → (switchSent p.sizes p.others).size = k)

set_option maxRecDepth 1000000 in
/-- **At the written seats.** -/
theorem oddRoleW : ((List.range 12).all (oddRole seatsAllFull)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **At the written places.** -/
theorem oddSizeW : (placesW.all (oddSize 5)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at 6 in place of 5 the test says no. -/
theorem oddSizeW_six : (placesW.all (oddSize 6)) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at message 2 of these sendings no seat has the role own 0. -/
theorem oddRoleW_two :
    ((List.range 12).any fun g =>
      (switchSeatIn seatsAllFull (2 * g + 1) 2).map (·.role) == some (Role.own 0)) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at message 3 of the sendings into the even links no seat has the role own 0. -/
theorem oddRoleW_even :
    ((List.range 11).any fun g =>
      (switchSeatIn seatsAllFull (2 * g + 2) 3).map (·.role) == some (Role.own 0)) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Twelve written places have an odd link below 24: so `oddSizeW` is not idle. -/
theorem oddSizeW_bites :
    (placesW.filter fun p => p.link % 2 == 1 && decide (p.link < 24)).length = 12 := by
  decide +kernel

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **Message 3 of the switch into an odd link below 24 bears the number of the link's own
message 0.** -/
theorem num3_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, ∀ g, g < 12 → p.link = 2 * g + 1 →
      switchNum Zp p 3 = P5J.At.num Zp (2 * g + 1) 0 := by
  intro p hp g hg hl
  have hp' : p ∈ placesW := by
    rw [← places_at_head h O]
    exact hp
  have hs : (switchSent p.sizes p.others).size = 5 :=
    of_decide_eq_true (List.all_eq_true.1 oddSizeW p hp') (by omega) (by omega)
  have e := ownNum_at_head h O p hp 3 0 (by rw [hs]; omega) (by
    rw [pseatsAll_at_head h, hl]
    exact beq_iff_eq.1 (List.all_eq_true.1 oddRoleW g (List.mem_range.2 hg)))
  rw [hl] at e
  exact e

end ProofFile.Honest.K2.Law

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.Law.oddRole
#print axioms ProofFile.Honest.K2.Law.oddSize
#print axioms ProofFile.Honest.K2.Law.oddRoleW
#print axioms ProofFile.Honest.K2.Law.oddSizeW
#print axioms ProofFile.Honest.K2.Law.oddSizeW_six
#print axioms ProofFile.Honest.K2.Law.oddRoleW_two
#print axioms ProofFile.Honest.K2.Law.oddRoleW_even
#print axioms ProofFile.Honest.K2.Law.oddSizeW_bites
#print axioms ProofFile.Honest.K2.Law.num3_at_head
