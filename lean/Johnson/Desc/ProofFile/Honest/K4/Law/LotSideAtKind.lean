-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/LotSideAtKind.lean: CONDITIONAL: on h, hG, hb and hk.

What is here. AT EVERY SUB-PROTOCOL OF THE FIRST CHAIN WHOSE PLACE IS OF THE KIND K4, K4's LOT HAS A
HALF AT THAT PLACE. The lot (`k4HLot`, Honest/K4/Part.lean) is the entry of the feed-forward layers'
own rounds (the sub-protocol K4) in a filling of the honest prover; a half is the prover's side for
one member of the chain. Under h : `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean: the library's hypothesis
on the public files; Zp is its public part, cF its first chain) and hG : `ProofFile.blankBy
ProofFile.pureRoad.links Zp` = some G₀ (G₀ is the ground that is made of the public part): for every
member b of the first chain's flat list with b.place.kind = .K4, b.place is among the places of the
lot's halves at Zp and G₀. It goes BY THE KIND, not by a number: whoever walks the chain and asks
«is there a side here» needs no group and no count. Two statements. The first says it as membership;
its proof is four calls: in scope the place of the flat list's member number i is the i-th of the
library's written list (`IM.place_at`, Johnson/IMR/PlacesScope.lean); that list is the one in the
driver's spelling (`Meaning.K2.placesW_linksFull`, Johnson/IMR/AtReachFits.lean); on it the kind K4
stands nowhere but at the twelve numbers 28 g + 4, at the place `k4PlaceAt g`, which is `IM.k4Place
g` written again (`OnBytes.Road.K4.k04_places_full`, Johnson/Road/K4/K04Places.lean, over
`k4AllB_full` there: a comparison by Lean's kernel); and at each of these twelve the lot has a half
(`k4HLot_place_iff`, Law/LotTwelve.lean). The second says the same as a search: `List.find?` over
the lot's halves, by the place, returns a half: the form in which a file that gathers all kinds'
sides asks it; it follows from the first by Lean's own `List.find?_isSome`. WHICH half the search
returns is not said there: that its place is b.place is Lean's own `List.find?_some`; that no second
half stands at that place: `k4HLot_places_once` (Law/LotOnce.lean); `lot_half_head`
(Law/HalfHead.lean) names the half, at a member that is laid by its number. General in cells,
weights and look. Statements and proofs.

  `k4HLot_side_at_kind`   **a half of K4's lot stands at the place of every member of the kind K4.**
  `k4HLot_find_at_kind`   the same as a search by the place: it returns a half.

Not shown here. THAT h CAN HOLD: the side library AtFullSide proves, with no hypothesis, that h has
a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean, whose
own Limits say what it is worth). hG asks nothing beyond h, as Law/LotTwelve.lean's head says. IT
SPEAKS OF THE LOT's OWN LIST, OF NO FILLING: that a filling holds this lot, and that a search over
the filling's halves finds this one, is not said here. Nothing on what a half sends, on any run or
thread. Nothing on a sub-protocol of another kind. THE FULL SIZE ALONE, AND THE FORMAT's EARLIER
HASH ALONE (`OnBytes.secondHashFunction`). THE GROUND IS THE ONE THAT IS MADE OF THE PUBLIC PART (hG). Beneath
it stand comparisons by Lean's own kernel (`k4AllB_full`; `LPFK9.linksW_full`,
Johnson/LPFK9R/SubsFull.lean, by `decide`, beneath `placesW_linksFull`; and those that
Law/LotTwelve.lean's head names); no independent checker that its writers know of has replayed them.
A LAW, NOT A PART: no
file that defines a part of the proof file's description may import this one. WHAT THIS FILE's
IMPORTS REACH, by a program's walk from import to import that stops, unopened, at every module under
Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose name begins
Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…: it stopped
at 65 modules under Johnson/Goal/, at 5 under Johnson/Bridge/ and at 1 that begins Cb.Bridge; it saw
46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and none of the three
names. What lies behind the 71 is not counted: all the numbers are floors. Nothing on soundness, on
completeness or on any other property.

Kin. No twin is known to its writers. `k4HLot_place_iff` (Law/LotTwelve.lean) has the halves' places
by the group's number; the library's `k04_places_full` (Johnson/Road/K4/K04Places.lean) has where
the kind K4 stands on the written list: this file joins the two. The library's `k04_sits_each`
(Johnson/Road/K4/K04SitsAll.lean; not imported here) has in its first clause what the first three
calls make: in scope, at an opening, a member of the first chain's flat list whose place is of the
kind K4 stands at a number 28 g + 4 with g < 12, at `k4PlaceAt g`. The other way round: each half's
place is of the kind K4 (`k4HLot_kind`, Law/LotKind.lean), and at an opening a member of the chain
stands at it (`k4HLot_member_open`, Law/LotNoStrayOpen.lean).
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.LotTwelve
import Johnson.IMR.AtReachFits
import Johnson.IMR.PlacesScope
import Johnson.Road.K4.K04Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The default instance `Inst.Model.Scl.ref` (a table of scales) is switched off in this file, so
that no statement picks a table of scales silently. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place} {W₀ Rc Tr X' : Type}

/-- CONDITIONAL: on h, hG, hb and hk. **A half of K4's lot stands at the place of every member of
the first chain's flat list whose place is of the kind K4.** -/
theorem k4HLot_side_at_kind (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) (cells : Tr → Cells)
    (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard)
    {b : Block TS ProofFile.Cl} (hb : b ∈ cF.blocksInOrder) (hk : b.place.kind = .K4) :
    b.place ∈ ((k4HLot (Rc := Rc) (X := X') cells weights look).halves Zp G₀).map (·.place) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hb
  have hp := IM.place_at h.scope h.reads O hi
  rw [Meaning.K2.placesW_linksFull] at hp
  obtain ⟨g, hg, -, e⟩ := OnBytes.Road.K4.k04_places_full i b.place hp hk
  exact (k4HLot_place_iff h hG cells weights look b.place).2
    (List.mem_map.2 ⟨g, List.mem_range.2 hg, e.symm⟩)

/-- CONDITIONAL: on h, hG, hb and hk. **The search by the place, over the halves of K4's lot,
returns a half at every member of the first chain's flat list whose place is of the kind K4.** -/
theorem k4HLot_find_at_kind (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) (cells : Tr → Cells)
    (weights : W₀ → Weights)
    (look : ProofFile.Pub → ProofFile.Ground → K4Pub → List Fmt.Drawn → Forest.Heard)
    {b : Block TS ProofFile.Cl} (hb : b ∈ cF.blocksInOrder) (hk : b.place.kind = .K4) :
    ∃ g, ((k4HLot (Rc := Rc) (X := X') cells weights look).halves Zp G₀).find?
      (fun y => y.place == b.place) = some g := by
  obtain ⟨z, hz, ez⟩ := List.mem_map.1
    (k4HLot_side_at_kind (Rc := Rc) (X' := X') h hG cells weights look hb hk)
  exact Option.isSome_iff_exists.1 (List.find?_isSome.2 ⟨z, hz, beq_iff_eq.2 ez⟩)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4HLot_side_at_kind
#print axioms ProofFile.Honest.K4.k4HLot_find_at_kind
