-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/KindTenPlaces.lean: where the kind K10, the closing of a segment, stands: under the head
the members of the first chain of that kind are just those at the 25 numbers 14 l + `IM.nAt l` + 5, l < 25, and neither the
shared nor the second chain has a member of the kind.

  `writtenPlaces_kindTen_at_borders`   every place of the kind K10 in the written list stands at one of the 25 numbers
  `writtenPlaces_borders_are_kindTen`  each of the 25 numbers holds a place of the kind
  `writtenPlaces_kindNine_elsewhere`, `writtenPlaces_twentySixth_is_not_kindTen`   the two tests can say no
  `writtenPlan_shared_no_kindTen`, `writtenPlan_second_no_kindTen`   the written description's two other chains
  **`kindTen_only_at_borders`**   under the head: a member of the first chain of the kind K10 stands at one of the 25 numbers
  `kindTen_at_each_border`      under the head: each of the 25 numbers holds a member of the kind
  `kindTen_not_in_shared`, `kindTen_not_in_second`   under the head

The closed facts are evaluated in Lean's kernel at the written lists.

Limits. The head is a premise. The full size and the older hash alone.
-/
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead
import Johnson.AtFull.ProofPlan.PlanAlike
import Johnson.P5J.PlacesPaid
import Johnson.IMR.WrittenList

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain KindName alike₂_place)
open P2Law.ProofPlan (WP)
open P5J (AtMgA TS)

/-- The number of the closing of segment l in the first chain's flat list. -/
abbrev closingNo (l : Nat) : Nat := 14 * l + IM.nAt l + 5

set_option maxRecDepth 1000000 in
/-- Every place of the kind K10 in the written list stands at one of the 25 numbers. A closed fact. -/
theorem writtenPlaces_kindTen_at_borders : ∀ j < P5J.At.ps.length,
    (P5J.At.ps[j]?).any (fun p => p.kind == KindName.K10) = true →
      j ∈ (List.range 25).map closingNo := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Each of the 25 numbers holds a place of the kind K10. A closed fact. -/
theorem writtenPlaces_borders_are_kindTen : ∀ l < 25,
    (P5J.At.ps[closingNo l]?).any (fun p => p.kind == KindName.K10) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- With the kind K9 in K10's stead the first sentence is false: the test on the kind is not idle. A closed fact. It says
no more than that. -/
theorem writtenPlaces_kindNine_elsewhere : ¬ ∀ j < P5J.At.ps.length,
    (P5J.At.ps[j]?).any (fun p => p.kind == KindName.K9) = true →
      j ∈ (List.range 25).map closingNo := by decide +kernel

set_option maxRecDepth 1000000 in
/-- At a twenty-sixth segment the sentence on the 25 numbers is false: the bound is not idle. A closed fact. It says no
more than that. -/
theorem writtenPlaces_twentySixth_is_not_kindTen : ¬ ∀ l < 26,
    (P5J.At.ps[closingNo l]?).any (fun p => p.kind == KindName.K10) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The written description's shared chain has no place of the kind K10. A closed fact. -/
theorem writtenPlan_shared_no_kindTen :
    ∀ p ∈ WP.shared.blocksInOrder.map (·.place), p.kind ≠ KindName.K10 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The written description's second chain has no place of the kind K10. A closed fact. -/
theorem writtenPlan_second_no_kindTen :
    ∀ p ∈ WP.second.blocksInOrder.map (·.place), p.kind ≠ KindName.K10 := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Under the head the place of the first chain's member number j is the written list's. -/
theorem writtenPlace_of_member (head : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {j : Nat} {blk : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[j]? = some blk) : P5J.At.ps[j]? = some blk.place := by
  have hp := P5J.At.places_paid head.scope head.reads head.laid
  have hq : (VerifiableInference.Desc.First.blockPlaces cF.blocksInOrder)[j]? = some blk.place := by
    unfold VerifiableInference.Desc.First.blockPlaces
    rw [List.getElem?_map, hb]
    rfl
  rw [hp] at hq
  exact hq

/-- **A member of the first chain of the kind K10 stands at one of the 25 numbers.** Conditional: the head. -/
theorem kindTen_only_at_borders (head : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {j : Nat} {blk : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[j]? = some blk) (hk : blk.place.kind = .K10) : ∃ l, l < 25 ∧ j = 14 * l + IM.nAt l + 5 := by
  have hq := writtenPlace_of_member head hb
  have hj : j < P5J.At.ps.length := (List.getElem?_eq_some_iff.1 hq).1
  have hm := writtenPlaces_kindTen_at_borders j hj (by
    rw [hq]
    show (blk.place.kind == KindName.K10) = true
    rw [hk]
    rfl)
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hm
  exact ⟨l, List.mem_range.1 hl, rfl⟩

/-- **Each of the 25 numbers holds a member of the first chain of the kind K10.** Conditional: the head. -/
theorem kindTen_at_each_border (head : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25) :
    ∃ blk, cF.blocksInOrder[14 * l + IM.nAt l + 5]? = some blk ∧ blk.place.kind = .K10 := by
  have hp := P5J.At.places_paid head.scope head.reads head.laid
  have t := writtenPlaces_borders_are_kindTen l hl
  cases hq : P5J.At.ps[closingNo l]? with
  | none =>
    rw [hq] at t
    cases t
  | some p =>
    rw [hq] at t
    have hk : p.kind = KindName.K10 := by
      simpa using t
    rw [← hp] at hq
    unfold VerifiableInference.Desc.First.blockPlaces at hq
    rw [List.getElem?_map] at hq
    obtain ⟨blk, hb, e⟩ := Option.map_eq_some_iff.1 hq
    exact ⟨blk, hb, by rw [e]; exact hk⟩

/-- **No member of the shared chain has the kind K10.** Conditional: the head. -/
theorem kindTen_not_in_shared (head : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ blk ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder, blk.place.kind ≠ KindName.K10 := by
  intro blk hb
  have e := alike₂_place _ _ (ProofFile.Honest.K14.planAlike_at_head head).shared
  have hm := List.mem_map_of_mem (f := (·.place)) hb
  rw [← e] at hm
  exact writtenPlan_shared_no_kindTen _ hm

/-- **No member of the second chain has the kind K10.** Conditional: the head. -/
theorem kindTen_not_in_second (head : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ blk ∈ (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder, blk.place.kind ≠ KindName.K10 := by
  intro blk hb
  have e := alike₂_place _ _ (ProofFile.Honest.K14.planAlike_at_head head).second
  have hm := List.mem_map_of_mem (f := (·.place)) hb
  rw [← e] at hm
  exact writtenPlan_second_no_kindTen _ hm

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.writtenPlaces_kindTen_at_borders
#print axioms ProofFile.Honest.K10.writtenPlaces_borders_are_kindTen
#print axioms ProofFile.Honest.K10.writtenPlaces_kindNine_elsewhere
#print axioms ProofFile.Honest.K10.writtenPlaces_twentySixth_is_not_kindTen
#print axioms ProofFile.Honest.K10.writtenPlan_shared_no_kindTen
#print axioms ProofFile.Honest.K10.writtenPlan_second_no_kindTen
#print axioms ProofFile.Honest.K10.writtenPlace_of_member
#print axioms ProofFile.Honest.K10.kindTen_only_at_borders
#print axioms ProofFile.Honest.K10.kindTen_at_each_border
#print axioms ProofFile.Honest.K10.kindTen_not_in_shared
#print axioms ProofFile.Honest.K10.kindTen_not_in_second
