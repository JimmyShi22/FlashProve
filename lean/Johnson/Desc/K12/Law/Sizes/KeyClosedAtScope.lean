-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Sizes/KeyClosedAtScope.lean: for the three later places of the proximity test
in a key file: where the planner's sizes of a key are the typed ones and a made place has the
declared rounds of the closed place (Johnson/Desc/K12/Law/PlacesKeyFull.lean), ITS SEVEN NUMBERS ARE
THE CLOSED PLACE's; and `ClosedL` (Johnson/Desc/K12/Coin/LawAtLight.lean: four tests with code and
the place's chain at 2⁻¹ ^ 128) goes over to it. Statements and proofs; no definition.

Main names.
  `nums_KU`, `nums_KO`, `nums_KW`: the numbers, whole: at the folded row's place, at Omega's place
    where the plan has one, and at the place of the own test.
  `closedL_KU`, `closedL_KO`, `closedL_KW`: `ClosedL` there.
What each asks. hk, hset: the key's sizes are `keyFull`, the setting is `setAt`. h: what
`Key.laterPlaces` returns. ONE DEBT ON THE MADE PLACE: hR: its declared rounds are the closed
place's. For `ClosedL` besides: hp: the block's own test on the plan at the made place.
How. Four numbers (rows, work, stages, own mask) are read off the sizes (`later_of_full`,
KeyAtScope.lean, against `held_KU` and its fellows, Johnson/Desc/K12/Law/RoundsAtKeyPlaces.lean).
Three (the trees of the group, the first free own number, the first tree's number) are read off the
declared rounds (`nums_of_rounds`, Johnson/Desc/K12/Law/NumsOfRounds.lean, at `rounds_KUFull` and
its fellows, Johnson/Desc/K12/Law/StretchKeyFull.lean). The chain: `key_later_more`. Then one call
of `ClosedL.of_reads` (ClosedAtScope.lean).
What it is not. hR is paid nowhere here. No law and no bound by itself: `ClosedL`'s own laws
(LawAtLight.lean) are to be called on it. The round "BAT" stands in front of the place's chain and
is not in the chain's condition: its number is priced by `ClosedL`'s field `bat`; the law that this
number bounds the round's bad verifier messages is the game's. The first chain's own test is not
here. No soundness is claimed. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.Sizes.KeyAtScope
import Johnson.Desc.K12.Law.Sizes.ClosedAtScope
import Johnson.Desc.K12.Law.RoundsAtKeyPlaces
import Johnson.Desc.K12.Law.StretchKeyFull
import Johnson.Desc.K12.Law.NumsOfRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K.Sizes
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Coin (ClosedL)
open H2K.Member (piKUFull piKOFull piKWFull rKUFull rKOFull rKWFull setAt)

section
variable {m : Johnson.G.OfPlan.Made} {P : VerifiableInference.Desc.Key.LaterPlaces}
  (hk : m.p.chains.made.sized.key = Lk6.AtPlan.keyFull) (hset : m.p.chains.made.sized.set = setAt)
  (h : VerifiableInference.Desc.Key.laterPlaces m = .ok P)
include hk hset h

/-! ## 1. The numbers, whole -/

/-- **The folded row's place.** -/
theorem nums_KU
    (hR : H2U.roundsOfNums P.U.nums = H2U.roundsOfNums piKUFull.nums) :
    P.U.nums = piKUFull.nums := by
  obtain ⟨e1, e2, e3, e4, _⟩ := (later_of_full hk hset h).1
  obtain ⟨g1, g2, g3, g4, _⟩ := H2K.Pub.held_KU
  have hs := e1.trans g1.symm
  have hm := e4.trans g4.symm
  obtain ⟨f1, f2, f3⟩ := nums_of_rounds (hR.trans H2K.Member.rounds_KUFull)
    H2K.Member.rounds_KUFull hs hm
  exact nums_ext (e2.trans g2.symm) (e3.trans g3.symm) hs hm f1 f2 f3

/-- **Omega's place, where the plan has one.** -/
theorem nums_KO (nO : H2U.PlaceNums) (hO : P.O = some nO)
    (hR : H2U.roundsOfNums nO.nums = H2U.roundsOfNums piKOFull.nums) :
    nO.nums = piKOFull.nums := by
  obtain ⟨e1, e2, e3, e4, _⟩ := (later_of_full hk hset h).2.2 nO hO
  obtain ⟨g1, g2, g3, g4, _⟩ := H2K.Pub.held_KO
  have hs := e1.trans g1.symm
  have hm := e4.trans g4.symm
  obtain ⟨f1, f2, f3⟩ := nums_of_rounds (hR.trans H2K.Member.rounds_KOFull)
    H2K.Member.rounds_KOFull hs hm
  exact nums_ext (e2.trans g2.symm) (e3.trans g3.symm) hs hm f1 f2 f3

/-- **The place of the own test.** -/
theorem nums_KW
    (hR : H2U.roundsOfNums P.W.nums = H2U.roundsOfNums piKWFull.nums) :
    P.W.nums = piKWFull.nums := by
  obtain ⟨e1, e2, e3, e4, _⟩ := (later_of_full hk hset h).2.1
  obtain ⟨g1, g2, g3, g4, _⟩ := H2K.Pub.held_KW
  have hs := e1.trans g1.symm
  have hm := e4.trans g4.symm
  obtain ⟨f1, f2, f3⟩ := nums_of_rounds (hR.trans H2K.Member.rounds_KWFull)
    H2K.Member.rounds_KWFull hs hm
  exact nums_ext (e2.trans g2.symm) (e3.trans g3.symm) hs hm f1 f2 f3

/-! ## 2. `ClosedL` -/

variable (place : Place)

/-- **The folded row's place.** -/
theorem closedL_KU
    (hp : (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt place P.U) : Block T12 Unit).planOk = true)
    (hR : H2U.roundsOfNums P.U.nums = H2U.roundsOfNums piKUFull.nums) :
    ClosedL (H2U.proximityTestParametersAt place P.U) rKUFull 1 0 0 H2K.Pub.TKUFull := by
  have hn := H2K.Made.nums_of_planOk place P.U hp
  have e := nums_KU hk hset h hR
  refine ClosedL.of_reads hp ?_ ?_ ?_ ?_ ?_ ?_ H2K.Pub.closed_KUFull.light
  · rw [hn, e]
  · rw [hn, e]
  · rw [hn, e]
  · rw [hn, e]
  · rw [hn, e]
  · rw [chain_of_planOk place P.U hp]
    exact (key_later_more h).1.1

/-- **Omega's place, where the plan has one.** -/
theorem closedL_KO (nO : H2U.PlaceNums) (hO : P.O = some nO)
    (hp : (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt place nO) : Block T12 Unit).planOk = true)
    (hR : H2U.roundsOfNums nO.nums = H2U.roundsOfNums piKOFull.nums) :
    ClosedL (H2U.proximityTestParametersAt place nO) rKOFull 1 0 0 H2K.Pub.TKOFull := by
  have hn := H2K.Made.nums_of_planOk place nO hp
  have e := nums_KO hk hset h nO hO hR
  refine ClosedL.of_reads hp ?_ ?_ ?_ ?_ ?_ ?_ H2K.Pub.closed_KOFull.light
  · rw [hn, e]
  · rw [hn, e]
  · rw [hn, e]
  · rw [hn, e]
  · rw [hn, e]
  · rw [chain_of_planOk place nO hp]
    exact ((key_later_more h).2.2 nO hO).1

/-- **The place of the own test.** -/
theorem closedL_KW
    (hp : (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt place P.W) : Block T12 Unit).planOk = true)
    (hR : H2U.roundsOfNums P.W.nums = H2U.roundsOfNums piKWFull.nums) :
    ClosedL (H2U.proximityTestParametersAt place P.W) rKWFull 2 6 2 H2K.Pub.TKWFull := by
  have hn := H2K.Made.nums_of_planOk place P.W hp
  have e := nums_KW hk hset h hR
  refine ClosedL.of_reads hp ?_ ?_ ?_ ?_ ?_ ?_ H2K.Pub.closed_KWFull.light
  · rw [hn, e]
  · rw [hn, e]
  · rw [hn, e]
  · rw [hn, e]
  · rw [hn, e]
  · rw [chain_of_planOk place P.W hp]
    exact (key_later_more h).2.1

end

end H2K.Sizes

#print axioms H2K.Sizes.nums_KU
#print axioms H2K.Sizes.nums_KO
#print axioms H2K.Sizes.nums_KW
#print axioms H2K.Sizes.closedL_KU
#print axioms H2K.Sizes.closedL_KO
#print axioms H2K.Sizes.closedL_KW
