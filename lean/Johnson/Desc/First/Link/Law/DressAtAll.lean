-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/Desc/First/Link/Law/DressAtAll.lean (kinds K10 and K2): IN WHICH DRESS THE ITEM «carry l»
IS ASKED, AT ALL 25 LINKS, UNDER THE HEAD ALONE: the sort of the place at which the item is spent,
`(ProofFile.pAtK2 Zp l).stands`. Theorems: joins of earlier theorems.

Why. `carryAtZ` (Top/H0/K2Caller/CarryClosed.lean) goes through a way in (`doorZ`) and a front
  (`K2.frontAt`, K2Hears/Long.lean) that split on that sort; and `ProofFile.pAtK2`
  (Desc/ProofFile/CarryAt.lean) answers dead numbers, IN A LINK's DRESS, where the plan has no place
  for the group. At l = 24 a link's dress would ask the shape's link 25, which is not there: the
  item would be false and K10's field hCar idle there; the library had «not the head's» at 24 under
  the head, and «the finish's» under a named test alone.

  `way_at`: a step inside this file, ON THE PLACE's SORT ALONE: at the switch's number i (a place of
    kind K2 of the written list) there is some `enter` at which WayAt (P1K2R/TiesOneFour.lean) holds
    of the place's numbers. OF THE WAY IN THAT SAYS NOTHING: WayAt speaks of `enter` only where
    `enter` returns, and nothing here ties `enter` to the seated block, so one that always refuses
    would serve. It is one conjunct of k02_sits7_pAt_at (P1K2R/ListsAtConst.lean), without the
    conjunct Sits that ties `enter` to the block; that theorem's two premises are paid under the
    head: the test on the places by spots_atAll, «25 links» by links25_open (Loose/H2K12/).
  `stands_finish_atAll`: **(ProofFile.pAtK2 Zp 24).stands = .finish.**
  `stands_link_atAll`: **l < 23 → (ProofFile.pAtK2 Zp l).stands = .link.** (At 23: hs_atAll,
    Loose/H2K12/HsAtAll.lean: the head's.)
Limits. On the place's sort alone: that the way in or the front answers at any state is not said
  here. Under a head (P5J/MgAtAll.lean): a member of it is proved at `storedPublicFiles` and `zGap` alone (at
  secondHashFunction; side library AtFullSide/Top/). Nothing on soundness.

-/
import Johnson.P1K2R.ListsAtConst
import Johnson.Loose.H2K12.HsAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain KindName)
open VerifiableInference.Desc.First.K2Caller (WayAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The place's sort, at a switch's number, under the head alone. Of the way in nothing is said:
`enter` is bound by ∃ alone, and WayAt speaks of it only where it returns. -/
theorem AtMgA.way_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (i : ℕ)
    (a : VerifiableInference.Desc.Place) (ha : At.ps[i]? = some a) (hk : a.kind = KindName.K2) :
    ∃ enter, WayAt (P1K2.mOf i) enter (ProofFile.pAtK2 Zp (P1K2.mOf i)) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨_, enter, _, _, _, _, _, _, w, _, _⟩ := P1K2.k02_sits7_pAt_at h.toAtMg
    (H2K12.spots_atAll h (pins_of_laid h.scope h.laid).2)
    (H2K12.links25_open h.scope h.reads O h.laid.planOk) i a ha hk
  exact ⟨enter, w⟩

/-- **AT LINK 24 THE ITEM IS ASKED IN THE FINISH's DRESS.** -/
theorem AtMgA.stands_finish_atAll (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (ProofFile.pAtK2 Zp 24).stands = .finish := by
  obtain ⟨a, ha, hk⟩ : ∃ a, At.ps[353]? = some a ∧ a.kind = KindName.K2 := by decide +kernel
  obtain ⟨_, w⟩ := h.way_at 353 a ha hk
  have e : P1K2.mOf 353 = 24 := by decide
  rw [e] at w
  rcases w with ⟨c, -, -⟩ | ⟨c, -, -⟩ | ⟨-, s, -⟩
  · omega
  · omega
  · exact s

/-- **AT THE LINKS BELOW 23 IN A LINK's.** -/
theorem AtMgA.stands_link_atAll (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : ℕ) (hl : l < 23) :
    (ProofFile.pAtK2 Zp l).stands = .link := by
  have hp : ∀ l, l < 23 → ∃ a, At.ps[14 * (l + 1) + 2]? = some a ∧ a.kind = KindName.K2 := by
    decide +kernel
  obtain ⟨a, ha, hk⟩ := hp l hl
  obtain ⟨_, w⟩ := h.way_at (14 * (l + 1) + 2) a ha hk
  have e : P1K2.mOf (14 * (l + 1) + 2) = l := by
    unfold P1K2.mOf
    rw [if_neg (by omega), if_neg (by omega)]
    omega
  rw [e] at w
  rcases w with ⟨-, s, -⟩ | ⟨c, -, -⟩ | ⟨c, -, -⟩
  · exact s
  · omega
  · omega

end P5J

#print axioms P5J.AtMgA.way_at
#print axioms P5J.AtMgA.stands_finish_atAll
#print axioms P5J.AtMgA.stands_link_atAll
