-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/Link24Written.lean: THE SWITCH INTO LINK 24, THE OUTPUT HEAD's:
FIVE NUMBERS OF ITS PLACE AND OF ITS MESSAGE NUMBER 2, AS A PUBLIC TEST; ITS YES AT THE WRITTEN LIST
`placesW` (PlacesWritten.lean of this folder) BY AN EVALUATION IN LEAN's KERNEL, AND SO, UNDER THE
LIBRARY's HYPOTHESIS ON THE PUBLIC FILES AND THE OPENING, AT THE LIST `switchPlaces`; THAT JUST ONE
PLACE OF EITHER LIST HAS THAT LINK; AND THAT MESSAGE NUMBER 2 THERE IS THE LINK's OWN MESSAGE 0. One
definition. Lemmas; none of the library's goals.

  `atLink24`             the test: a place with link 24 is ⟨1, some 24, 2, K2⟩; it announces 4
                         messages; message 2 has one mask row; its mask code's message length is
                         8192; its mask rows' entries begin at element 439 of the sending's elements
                         of the extension field (`maskBase`, MaskCoin.lean of this folder). AT A
                         PLACE WITH ANOTHER LINK IT SAYS YES AND ASKS NOTHING
  `atLink24W`            it accepts at each place of the written list
  `link24W_one`          just one written place has link 24: so the line above is not idle
  `atLink24W_can_fail`   A CONTROL: at that place with the mask rows of its field others raised by
                         one (`moreMaskOthers`, OneMaskRowAtHead.lean of this folder) the test says
                         no
  `role24W`              in the written list of seats the seat of message 2 of the sending "link 24,
                         moment 0" has the role own 0
  `atLink24_gives`       the test's yes at a place with link 24: the five equations
  `atLink24_at_head`     at each place of `switchPlaces` Zp Bs.G₀
  `link24_at_head`       just one place of that list has link 24
  `num24_at_head`        there `switchNum` Zp p 2 is `P5J.At.num` Zp 24 0

WHAT IT IS NOT. Facts on the written plan's shapes, codes and seats: no state, no run, no input; no
lot of messages is laid. That the hypothesis on the public files can be met is not said here.

Limits. Four evaluations, rewritings, an unfolding. The written lists are the full size's; the
hypothesis on the public files is taken at the earlier of the format's two hash functions
(`OnBytes.secondHashFunction`). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchNumsAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.OneMaskRowAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskCoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open P5T (Role seatsAllFull)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **A PUBLIC TEST**: five numbers at a place with link 24; nothing at another. -/
def atLink24 (p : SwitchPlace) : Bool :=
  p.link != 24 ||
    (p.place == ⟨1, some 24, 2, .K2⟩ && (switchSent p.sizes p.others).size == 4 &&
      ((switchSent p.sizes p.others).getD 2 default).shape.maskRows == 1 &&
      (p.sizes.codes.mask.getD
        ((switchSent p.sizes p.others).getD 2 default).shape.maskCode default).ell == 8192 &&
      maskBase p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars) 2 == 439)

set_option maxRecDepth 1000000 in
/-- **The test accepts at each place of the written list.** -/
theorem atLink24W : (placesW.all atLink24) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Just one written place has link 24. -/
theorem link24W_one : (placesW.filter fun p => p.link == 24).length = 1 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A control: the test can say no next to the written list.** -/
theorem atLink24W_can_fail :
    (((placesW.filter fun p => p.link == 24).map moreMaskOthers).all atLink24) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The seat of message 2 of the sending "link 24, moment 0" has the role own 0. -/
theorem role24W : (switchSeatIn seatsAllFull 24 2).map (·.role) = some (Role.own 0) := by
  decide +kernel

/-- **What the test's yes gives at a place with link 24.** -/
theorem atLink24_gives {p : SwitchPlace} (hp : atLink24 p = true) (hl : p.link = 24) :
    p.place = ⟨1, some 24, 2, .K2⟩ ∧ (switchSent p.sizes p.others).size = 4 ∧
      ((switchSent p.sizes p.others).getD 2 default).shape.maskRows = 1 ∧
      (p.sizes.codes.mask.getD
        ((switchSent p.sizes p.others).getD 2 default).shape.maskCode default).ell = 8192 ∧
      maskBase p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars) 2 = 439 := by
  unfold atLink24 at hp
  rw [hl] at hp
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨hp.1.1.1.1, hp.1.1.1.2, hp.1.1.2, hp.1.2, hp.2⟩

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **Under the head and the opening: at each place of the kind's list.** -/
theorem atLink24_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, atLink24 p = true := by
  rw [places_at_head h O]
  exact List.all_eq_true.1 atLink24W

/-- Just one place of the kind's list has link 24. -/
theorem link24_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ((switchPlaces Zp Bs.G₀).filter fun p => p.link == 24).length = 1 := by
  rw [places_at_head h O]
  exact link24W_one

/-- **Message 2 of the switch into link 24 bears the number of the link's own message 0.** -/
theorem num24_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, p.link = 24 → switchNum Zp p 2 = P5J.At.num Zp 24 0 := by
  intro p hp hl
  have g := atLink24_gives (atLink24_at_head h O p hp) hl
  have e := ownNum_at_head h O p hp 2 0 (by rw [g.2.1]; omega) (by
    rw [pseatsAll_at_head h, hl]
    exact role24W)
  rw [hl] at e
  exact e

end ProofFile.Honest.K2.Law

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.Law.atLink24
#print axioms ProofFile.Honest.K2.Law.atLink24W
#print axioms ProofFile.Honest.K2.Law.link24W_one
#print axioms ProofFile.Honest.K2.Law.atLink24W_can_fail
#print axioms ProofFile.Honest.K2.Law.role24W
#print axioms ProofFile.Honest.K2.Law.atLink24_gives
#print axioms ProofFile.Honest.K2.Law.atLink24_at_head
#print axioms ProofFile.Honest.K2.Law.link24_at_head
#print axioms ProofFile.Honest.K2.Law.num24_at_head
