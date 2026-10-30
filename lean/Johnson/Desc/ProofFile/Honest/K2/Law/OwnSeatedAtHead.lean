-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/OwnSeatedAtHead.lean: UNDER THE LIBRARY's HEAD THE PUBLIC TEST
`ownSeated` (LightHangsOnSized.lean of this folder) SAYS YES AT EACH PLACE OF THE KIND's LIST: each
own message of each switch's own sending has a seat among the switches'. By the writers of the merge
of the claims on the weights (sub-protocol K11). PUBLIC DATA ALONE: the written list of places, the
written shape of a request. One definition (a test). Lemmas; none of the library's goals.

  `ownListed` sh p      A PUBLIC TEST on a request's shape and a place: the segment into which the
                        switch leads has, at moment 0, a message of each number that the place's own
                        sending has an own message of. The list is `ownSeated`'s own
  `ownListedW`          its yes at the written shape at each place of the written list `placesW`
                        (PlacesWritten.lean of this folder), BY LEAN's KERNEL
  `ownListedW_can_fail` A CONTROL THAT SAYS NO: at the empty shape, at the same list
  `ownSeated_of_listed` general: at a place of the kind's list the yes of `ownListed` at the
                        ground's shape gives `ownSeated`'s: by `switchSeat_own` (OwnDataApart.lean
                        of this folder)
  `ownSeated_at_head`   UNDER THE HEAD AND THE OPENING: at each place of `switchPlaces` Zp Bs.G₀

By. `places_at_head` (PlacesWritten.lean): the kind's list is the written one. The ground's shape is
the written one: `IM.Open.first` (Johnson/IMR/SeatOpen.lean), `K13.Law.likeFull_in_scope`
(Johnson/HB/LLHARD/PlanInScope.lean), `K1.pin1_atAll` (Johnson/Desc/K1/Law/PinsAtHead.lean).

WHAT IT IS NOT. One premise of `light_congr` and `publicOk_of_light_at` (LightHangsOnSized.lean) is
paid at the head; their others are not touched. Nothing on what a seat's message holds.

Limits. THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE. TWO CLOSED FACTS BY EVALUATION IN LEAN's
KERNEL. The head and the opening are premises. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.LightHangsOnSized
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.K1.Law.TiesAtAll
import Johnson.Desc.K1.Law.PinsAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (LikeFull)
open VerifiableInference.PlanWritten (proofSizedFull)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **A PUBLIC TEST**: the segment has a message of moment 0 of each own message's number. -/
def ownListed (sh : OnBytes.Params.ReqShape) (p : SwitchPlace) : Bool :=
  (p.others.toList.take (p.others.size - 1)).zipIdx.all fun n => (msgNo sh p.link 0 n.2).isSome

set_option maxRecDepth 1000000 in
/-- **The test accepts at the written shape at each place of the written list.** -/
theorem ownListedW : (placesW.all (ownListed proofSizedFull.request)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A control: at the empty shape the test says no.** -/
theorem ownListedW_can_fail : (placesW.all (ownListed default)) = false := by decide +kernel

/-- At a place of the kind's list its yes at the ground's shape gives `ownSeated`'s. -/
theorem ownSeated_of_listed {Z : Pub} {G : Ground} {p : SwitchPlace} (hp : p ∈ switchPlaces Z G)
    (h : ownListed G.first.shape p = true) : ownSeated Z G p = true :=
  List.all_eq_true.2 fun n hn => switchSeat_own Z G p hp n.2 (List.all_eq_true.1 h n hn)

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)}

/-- **Under the head and the opening: at each place of the kind's list.** -/
theorem ownSeated_at_head (h : AtMgA OnBytes.secondHashFunction W D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∀ p ∈ switchPlaces Zp Bs.G₀, ownSeated Zp Bs.G₀ p = true := by
  intro p hp
  have hF : LikeFull Bs.G₀.first := by
    rw [O.first]
    exact K13.Law.likeFull_in_scope h.scope h.laid.pub (K1.pin1_atAll h)
  refine ownSeated_of_listed hp ?_
  rw [hF.shape]
  rw [places_at_head h.toAtMg O] at hp
  exact List.all_eq_true.1 ownListedW p hp

end ProofFile.Honest.K2.Law

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.Law.ownListed
#print axioms ProofFile.Honest.K2.Law.ownListedW
#print axioms ProofFile.Honest.K2.Law.ownListedW_can_fail
#print axioms ProofFile.Honest.K2.Law.ownSeated_of_listed
#print axioms ProofFile.Honest.K2.Law.ownSeated_at_head
