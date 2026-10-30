-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/OneMaskRowAtHead.lean: NO MESSAGE THAT A SWITCH ANNOUNCES HAS
MORE THAN ONE MASK ROW: A PUBLIC TEST, ITS YES AT EACH PLACE OF THE WRITTEN LIST `placesW`
(PlacesWritten.lean of this folder) BY AN EVALUATION IN LEAN's KERNEL, AND SO, UNDER THE LIBRARY's
HYPOTHESIS ON THE PUBLIC FILES AND THE OPENING, AT EACH PLACE OF THE LIST `switchPlaces`. Two
definitions (the test; a turned place for a control). Lemmas; none of the library's goals. In the
form of MaskOrOneAtHead.lean of this folder.

  `atMostOneMaskRow`          the test: each message of the place has at most one mask row
  `atMostOneMaskRowW`         it accepts at each place of the written list
  `oneMaskRowW_count`         of the written places' 132 messages 49 have just one mask row (83 have
                              none: `maskOrOneW_counts`, MaskOrOneAtHead.lean of this folder)
  `atMostOneMaskRowW_can_fail`   A CONTROL: at the first written place with the mask rows of its
                              field others raised by one (`moreMaskOthers`) the test says no; the
                              number of messages is the same
  `atMostOneMaskRow_at_head`  at each place of `switchPlaces` Zp Bs.G₀
  `maskRows_le_one`           its use: where the test accepts, message n of the place has at most
                              one mask row
  `maskRows_eq_one`           and just one, where it has any

Why. An entry number ν of a message's mask table lies in row ν modulo m at the place ν over m, m the
number of mask rows. At m = 1 that is row 0, place ν.

WHAT IT IS NOT. A fact on the shapes of the written plan's messages: no state, no run, no input; no
lot of messages is laid. AT A MESSAGE WITHOUT A MASK ROW (m = 0) ν modulo m is ν and ν over m is 0:
"row 0, place ν" is had only where the message has a mask row: `maskRows_eq_one` asks that. The
number of written places is 25 (`placesW_count`, PublicAtWritten.lean). That the hypothesis on the
public files can be met is not said here.

NEAR. `placeOneRow` (PlanAsks.lean of this folder): the like for the one message that rides with the
next fold.

Limits. Three evaluations, one rewriting, two unfoldings. The written list is the full size's; the
hypothesis on the public files is taken at the format's second hash function. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open P5J (AtMg F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **A PUBLIC TEST**: each message of the place has at most one mask row. -/
def atMostOneMaskRow (p : SwitchPlace) : Bool :=
  (switchSent p.sizes p.others).toList.all fun x => decide (x.shape.maskRows ≤ 1)

/-- For a control: the mask rows of the messages in the field others raised by one. -/
def moreMaskOthers (p : SwitchPlace) : SwitchPlace :=
  { p with others := p.others.map fun x =>
      { x with shape := { x.shape with maskRows := x.shape.maskRows + 1 } } }

set_option maxRecDepth 1000000 in
/-- **The test accepts at each place of the written list.** -/
theorem atMostOneMaskRowW : (placesW.all atMostOneMaskRow) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- How many of the written places' messages have just one mask row. -/
theorem oneMaskRowW_count :
    ((placesW.flatMap fun p => (switchSent p.sizes p.others).toList).countP
      fun x => x.shape.maskRows == 1) = 49 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A control: the test can say no next to the written list.** -/
theorem atMostOneMaskRowW_can_fail :
    (((placesW.take 1).map moreMaskOthers).all atMostOneMaskRow) = false ∧
      (((placesW.take 1).map moreMaskOthers).map fun p => (switchSent p.sizes p.others).size) =
        ((placesW.take 1).map fun p => (switchSent p.sizes p.others).size) := by decide +kernel

/-- **Its use.** -/
theorem maskRows_le_one {p : SwitchPlace} (hp : atMostOneMaskRow p = true) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size) :
    ((switchSent p.sizes p.others).getD n default).shape.maskRows ≤ 1 := by
  have h := List.all_eq_true.1 hp ((switchSent p.sizes p.others).getD n default) (by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hn]
    exact Array.getElem_mem_toList hn)
  exact of_decide_eq_true h

/-- Just one, where the message has any. -/
theorem maskRows_eq_one {p : SwitchPlace} (hp : atMostOneMaskRow p = true) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size)
    (hm : ((switchSent p.sizes p.others).getD n default).shape.maskRows ≠ 0) :
    ((switchSent p.sizes p.others).getD n default).shape.maskRows = 1 := by
  have := maskRows_le_one hp hn
  omega

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **Under the head and the opening: at each place of the kind's list.** -/
theorem atMostOneMaskRow_at_head (h : AtMg OnBytes.secondHashFunction W D r Zp Np cF)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, atMostOneMaskRow p = true := by
  rw [places_at_head h O]
  exact List.all_eq_true.1 atMostOneMaskRowW

end ProofFile.Honest.K2.Law

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.Law.atMostOneMaskRow
#print axioms ProofFile.Honest.K2.Law.moreMaskOthers
#print axioms ProofFile.Honest.K2.Law.atMostOneMaskRowW
#print axioms ProofFile.Honest.K2.Law.oneMaskRowW_count
#print axioms ProofFile.Honest.K2.Law.atMostOneMaskRowW_can_fail
#print axioms ProofFile.Honest.K2.Law.maskRows_le_one
#print axioms ProofFile.Honest.K2.Law.maskRows_eq_one
#print axioms ProofFile.Honest.K2.Law.atMostOneMaskRow_at_head
