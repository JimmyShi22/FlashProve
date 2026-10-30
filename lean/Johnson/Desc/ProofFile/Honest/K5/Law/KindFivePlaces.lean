-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/KindFivePlaces.lean: under the library's head, the first chain's
members of the kind K5 (an attention segment's own rounds) are the twelve at the numbers borderOf g,
g below 12, and no others; the shared chain and the second chain have none. Closed facts on the written
list of places and on the written description, and three laws that carry them to the description at the
head. No definition.

  writtenPlaces_kindFive_at_borders   every place of the kind K5 in the written list stands at one of
                                      the twelve numbers
  writtenPlaces_borders_are_kindFive  each of the twelve numbers holds a place of the kind K5
  writtenPlaces_kindFour_elsewhere    the first sentence with the kind K4 in K5's stead is false, so
                                      the test on the kind is not idle
  writtenPlan_shared_no_kindFive, writtenPlan_second_no_kindFive   the written description's shared
                                      and second chains have no place of the kind K5
  writtenPlan_shared_has_kindFourteen, writtenPlan_second_has_kindFourteen   each of these with the
                                      kind K14 in K5's stead is false
  writtenPlaces_thirteenth_is_not_kindFive   the second sentence at a thirteenth group is false
  kindFive_at_each_border             under the head: each of the twelve numbers holds a member of the
                                      first chain of the kind K5
  kindFive_only_at_borders            under the head: a member of the first chain of the kind K5 stands
                                      at one of the twelve numbers
  kindFive_not_in_shared, kindFive_not_in_second   under the head: no member of the other two chains
                                      has the kind K5

How. The head ties the first chain's list of places to the written list (P5J.At.places_paid), and the
head's description to the written description, place by place (planAlike_at_head).

The first chain's flat list of the head's description is cF.blocksInOrder by its definition (sits_head,
Thread/FirstHead.lean).

Limits. Conditional on the head. The closed facts are decided by Lean's kernel by evaluation at the
written lists. Nothing is said of what a member does.
This file proves nothing about soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.NoStrayThree
import Johnson.Desc.ProofFile.Honest.K5.Law.Seated
import Johnson.Desc.ProofFile.Honest.K5.Law.Member
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead
import Johnson.AtFull.ProofPlan.PlanAlike

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain KindName alike₂_place)
open P2Law.ProofPlan (WP)
open P5J (AtMgA TS)

set_option maxRecDepth 1000000 in
/-- Every place of the kind K5 in the written list stands at one of the twelve numbers. A closed
fact. -/
theorem writtenPlaces_kindFive_at_borders : ∀ j < P5J.At.ps.length,
    (P5J.At.ps[j]?).any (fun p => p.kind == KindName.K5) = true →
      j ∈ (List.range 12).map borderOf := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Each of the twelve numbers holds a place of the kind K5. A closed fact. -/
theorem writtenPlaces_borders_are_kindFive : ∀ g < 12,
    (P5J.At.ps[borderOf g]?).any (fun p => p.kind == KindName.K5) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- With the kind K4 in K5's stead the first sentence is false: the test on the kind is not idle. A
closed fact. It says no more than that. -/
theorem writtenPlaces_kindFour_elsewhere : ¬ ∀ j < P5J.At.ps.length,
    (P5J.At.ps[j]?).any (fun p => p.kind == KindName.K4) = true →
      j ∈ (List.range 12).map borderOf := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The written description's shared chain has no place of the kind K5. A closed fact. -/
theorem writtenPlan_shared_no_kindFive :
    ∀ p ∈ WP.shared.blocksInOrder.map (·.place), p.kind ≠ KindName.K5 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The written description's second chain has no place of the kind K5. A closed fact. -/
theorem writtenPlan_second_no_kindFive :
    ∀ p ∈ WP.second.blocksInOrder.map (·.place), p.kind ≠ KindName.K5 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- At a thirteenth group the sentence on the twelve numbers is false: the bound is not idle. A closed
fact. It says no more than that. -/
theorem writtenPlaces_thirteenth_is_not_kindFive : ¬ ∀ g < 13,
    (P5J.At.ps[borderOf g]?).any (fun p => p.kind == KindName.K5) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- With the kind K14 in K5's stead the sentence on the second chain is false: the test is not idle. A
closed fact. It says no more than that. -/
theorem writtenPlan_second_has_kindFourteen :
    ¬ ∀ p ∈ WP.second.blocksInOrder.map (·.place), p.kind ≠ KindName.K14 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- With the kind K14 in K5's stead the sentence on the shared chain is false: the test is not idle. A
closed fact. It says no more than that. -/
theorem writtenPlan_shared_has_kindFourteen :
    ¬ ∀ p ∈ WP.shared.blocksInOrder.map (·.place), p.kind ≠ KindName.K14 := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **No member of the shared chain has the kind K5.** Conditional: the head. -/
theorem kindFive_not_in_shared (head : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ blk ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder, blk.place.kind ≠ KindName.K5 := by
  intro blk hb
  have e := alike₂_place _ _ (ProofFile.Honest.K14.planAlike_at_head head).shared
  have hm := List.mem_map_of_mem (f := (·.place)) hb
  rw [← e] at hm
  exact writtenPlan_shared_no_kindFive _ hm

/-- **No member of the second chain has the kind K5.** Conditional: the head. -/
theorem kindFive_not_in_second (head : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ blk ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder, blk.place.kind ≠ KindName.K5 := by
  intro blk hb
  have e := alike₂_place _ _ (ProofFile.Honest.K14.planAlike_at_head head).second
  have hm := List.mem_map_of_mem (f := (·.place)) hb
  rw [← e] at hm
  exact writtenPlan_second_no_kindFive _ hm

/-- **Each of the twelve numbers holds a member of the first chain of the kind K5.** Conditional: the
head. -/
theorem kindFive_at_each_border (head : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : Nat} (hg : g < 12) :
    ∃ blk, cF.blocksInOrder[borderOf g]? = some blk ∧ blk.place.kind = .K5 := by
  obtain ⟨blk, _, hb, -, decides⟩ := k5_member head hg
  exact ⟨blk, hb, by rw [decides.place]⟩

/-- **A member of the first chain of the kind K5 stands at one of the twelve numbers.** Conditional:
the head. -/
theorem kindFive_only_at_borders (head : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {j : Nat}
    {blk : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[j]? = some blk) (hk : blk.place.kind = .K5) :
    ∃ g, g < 12 ∧ j = borderOf g := by
  have hp := P5J.At.places_paid head.scope head.reads head.laid
  have hq : (VerifiableInference.Desc.First.blockPlaces cF.blocksInOrder)[j]? = some blk.place := by
    unfold VerifiableInference.Desc.First.blockPlaces
    rw [List.getElem?_map, hb]
    rfl
  rw [hp] at hq
  have hj : j < P5J.At.ps.length := (List.getElem?_eq_some_iff.1 hq).1
  have hm := writtenPlaces_kindFive_at_borders j hj (by
    rw [hq]
    show (blk.place.kind == KindName.K5) = true
    rw [hk]
    rfl)
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
  exact ⟨g, List.mem_range.1 hg, rfl⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.writtenPlaces_kindFive_at_borders
#print axioms ProofFile.Honest.K5.writtenPlaces_borders_are_kindFive
#print axioms ProofFile.Honest.K5.writtenPlaces_kindFour_elsewhere
#print axioms ProofFile.Honest.K5.writtenPlan_shared_no_kindFive
#print axioms ProofFile.Honest.K5.writtenPlan_second_no_kindFive
#print axioms ProofFile.Honest.K5.writtenPlan_shared_has_kindFourteen
#print axioms ProofFile.Honest.K5.writtenPlan_second_has_kindFourteen
#print axioms ProofFile.Honest.K5.writtenPlaces_thirteenth_is_not_kindFive
#print axioms ProofFile.Honest.K5.kindFive_at_each_border
#print axioms ProofFile.Honest.K5.kindFive_only_at_borders
#print axioms ProofFile.Honest.K5.kindFive_not_in_shared
#print axioms ProofFile.Honest.K5.kindFive_not_in_second
