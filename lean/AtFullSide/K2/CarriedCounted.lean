-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K2/CarriedCounted.lean: THE CLOSED FACTS OF CarriedAtTheBook.lean OF THIS FOLDER, EACH
WITH THE COUNT OF THE LIST OVER WHICH IT RUNS BESIDE IT: THE WRITTEN LIST placesW HAS 25 MEMBERS, AT
25 DIFFERENT PLACES. Why: `openingCarriedW` says "at all members of placesW", its five controls "at
no member": AT AN EMPTY LIST ALL SIX WOULD HOLD: the test's yes and its controls' no would then say
nothing. No definition. Five lemmas; none of the library's
goals. PUBLIC DATA ALONE.

  `placesW_places_nodup`, `placesW_places_bent`
      BY LEAN's KERNEL: the members' places are all different · a control: with the first member's
      place laid once more they are not
  `openingCarried_counted`
      25 members · at different places · the written first segment is one, its first sending has
      four messages, and the test says yes at every member
  `openingCarried_controls_counted`
      25 members · and each of the five controls says yes at none of them
  `carried_at_25`
      UNDER THE HEAD AND THE OPENING: the plan's own list of switches has 25 members at different
      places: so `carried_opening_at_book` speaks of 25 switches

By: `placesW_count` (Johnson/Desc/ProofFile/Honest/K2/Law/PlacesCount.lean, K2's authors') · the six
closed facts of CarriedAtTheBook.lean · `places_at_head` (PlacesWritten.lean). NEAR, another group
of authors': `switchPlaces_count` (AtFullSide/K14/SwitchesLend.lean; this library may not hold it):
the same count.

Limits. TWO CLOSED FACTS BY EVALUATION IN LEAN's KERNEL HERE, one a control; seven lie beneath. All
limits of CarriedAtTheBook.lean stand: the first four carried entries alone; owner, start and count.
Nothing on any property.
-/
import AtFullSide.K2.CarriedAtTheBook
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (parGF qFull)
open Johnson.Prover.Send (shapeAt)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.K2 (switchPlaces)
open ProofFile.Honest.K2.Law (placesW segsW places_at_head placesW_count)
open AtFullSide.K14 (rawAheadW)

set_option maxRecDepth 1000000 in
/-- **The written members' places are all different.** -/
theorem placesW_places_nodup : (placesW.map (·.place)).Nodup := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with the first member's place laid once more they are not. -/
theorem placesW_places_bent :
    ¬ ((placesW.map (·.place)).head?.toList ++ placesW.map (·.place)).Nodup := by decide +kernel

/-- **The closed fact with its list's count beside it.** -/
theorem openingCarried_counted :
    placesW.length = 25 ∧ (placesW.map (·.place)).Nodup ∧ (segsW.take 1).length = 1 ∧
      ((segsW.take 1).all fun Sg =>
        decide ((Sg.sent.headD #[]).size = 4) &&
          placesW.all (openingCarried rawAheadW parGF (K1.rideOf (K1.firstFold qFull)) Sg)) =
        true :=
  ⟨placesW_count, placesW_places_nodup, openingCarriedW.2, openingCarriedW.1⟩

/-- **The five controls with that count beside them**: each conjunct is its statement in
CarriedAtTheBook.lean, cut by program. -/
theorem openingCarried_controls_counted :
    placesW.length = 25 ∧
      ((placesW.any fun p => (List.range 4).any fun n =>
      entryRunIs (carriedW p) n openingAddr
        ⟨(K1.startR parGF (K1.rideOf (K1.firstFold qFull)) n).f,
          (K1.startR parGF (K1.rideOf (K1.firstFold qFull)) n).e + 1⟩
        (K1.dueMsg parGF.codes (shapeAt parGF n) (K1.rideOf (K1.firstFold qFull) n))) = false) ∧
      ((placesW.any fun p => (List.range 4).any fun n =>
      entryRunIs (carriedW p) n openingAddr
        ⟨(K1.startR parGF (K1.rideOf (K1.firstFold qFull)) n).f + 1,
          (K1.startR parGF (K1.rideOf (K1.firstFold qFull)) n).e⟩
        (K1.dueMsg parGF.codes (shapeAt parGF n) (K1.rideOf (K1.firstFold qFull) n))) = false) ∧
      ((placesW.any fun p => (List.range 4).any fun n =>
      entryRunIs (carriedW p) n openingAddr
        (K1.startR parGF (K1.rideOf (K1.firstFold qFull)) n)
        ⟨(K1.dueMsg parGF.codes (shapeAt parGF n) (K1.rideOf (K1.firstFold qFull) n)).f,
          (K1.dueMsg parGF.codes (shapeAt parGF n) (K1.rideOf (K1.firstFold qFull) n)).e + 1⟩) =
        false) ∧
      ((placesW.any fun p => (List.range 4).any fun n =>
      entryRunIs (carriedW p) (n + 1) openingAddr
        (K1.startR parGF (K1.rideOf (K1.firstFold qFull)) n)
        (K1.dueMsg parGF.codes (shapeAt parGF n) (K1.rideOf (K1.firstFold qFull) n))) = false) ∧
      ((placesW.any fun p => (List.range 4).any fun n =>
      entryRunIs (carriedW p) n ⟨⟨1, some 0, 1, .K1⟩, 1⟩
        (K1.startR parGF (K1.rideOf (K1.firstFold qFull)) n)
        (K1.dueMsg parGF.codes (shapeAt parGF n) (K1.rideOf (K1.firstFold qFull) n))) = false) :=
  ⟨placesW_count, openingCarriedW_bent_e, openingCarriedW_bent_f, openingCarriedW_bent_count,
    openingCarriedW_next, openingCarriedW_other⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- **Under the head and the opening the plan has 25 switches, at different places.** -/
theorem carried_at_25 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    (switchPlaces Zp Bs.G₀).length = 25 ∧ ((switchPlaces Zp Bs.G₀).map (·.place)).Nodup := by
  rw [places_at_head h.toAtMg O]
  exact ⟨placesW_count, placesW_places_nodup⟩

end AtFullSide.K2

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K2.placesW_places_nodup
#print axioms AtFullSide.K2.placesW_places_bent
#print axioms AtFullSide.K2.openingCarried_counted
#print axioms AtFullSide.K2.openingCarried_controls_counted
#print axioms AtFullSide.K2.carried_at_25
