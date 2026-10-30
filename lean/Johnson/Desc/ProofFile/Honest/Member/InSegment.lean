--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Member/InSegment.lean: for a lot's sub-protocol of a kind whose place
lies in a segment: a member of the first chain's flat list stands at its place, and it passes its
test on the plan where the proof file's IOP does. Statements with their proofs.

`plan_at_place` (Johnson/Desc/ProofFile/Honest/Member/Plan.lean) takes for premises a member of the
flat list and that it stands at the place. `stands_iff` (Stands.lean) says at which places a member
stands, by the driver's list of places, which hangs on the sorts of the segments. For a lot's
sub-protocol in a segment neither the member nor the segment's sort has to be supplied: `faultsAt`
has found nothing, so the sub-protocol stands at a place of the shape; the shape's places are the
driver's list at some value of its flag; a place of that list in segment l is one of that segment's
places, whatever the flag.
Main names:
  `stands_in_segment`: at `onlineDescription`, opened as `IM.Open` has it: a member of the flat list stands
    at the place of a lot's sub-protocol that is of a kind and lies in a segment.
  `plan_in_segment`: **where the IOP passes its tests on the plan, such a sub-protocol passes its
    own.**
Called from Johnson/IMR: `stands_in_shape`, `shape_places` (LinkSeat.lean), `base_made`
(PureJoin.lean), `flat_in_link` (CloseSeat.lean), `flat_of_link` (SameSpot.lean).

What is not claimed. Nothing at a place outside the segments (Stands.lean has three of them by
name). That the IOP passes its tests on the plan at any three files: a premise. Nothing on
soundness, completeness or hiding.

-/
import Johnson.Desc.ProofFile.Honest.Member.Plan
import Johnson.Desc.ProofFile.Honest.Member.Stands

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.AtPlace
open VerifiableInference.Desc (Block Chain FileDescription KindName)
open VerifiableInference.Desc.First (S)

variable {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Z : Pub} {Bs : PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : SharedSeat} {B : SecondSeat}

/-- A member of the flat list stands at the place of a lot's sub-protocol that is of a kind and lies
in a segment. -/
theorem stands_in_segment (O : IM.Open o pol lay KL F Z Bs base c A B) {L : Lot}
    (hL : L ∈ onlineFirstChainBlockTables Z) {b : Block S Cl} (hb : b ∈ L.blocks Bs.G₀)
    (hk : b.place.kind ≠ KindName.frame) {l : Nat} (hl : b.place.link = some l) :
    ∃ m ∈ c.blocksInOrder, m.place = b.place := by
  obtain ⟨e, he, ee⟩ := IM.stands_in_shape O.sound (mem_all O.made hL hb) hk
  obtain ⟨several, hpls⟩ := IM.shape_places (IM.base_made O.made).2.1
  have hmem : b.place ∈ VerifiableInference.Desc.First.flatPlacesOf (subsOf Z) several := by
    rw [← hpls, ← ee]
    exact List.mem_map.2 ⟨e, he, rfl⟩
  obtain ⟨sub, hsub, hin⟩ := IM.flat_in_link hmem hl
  exact (stands_iff O b.place).2 (IM.flat_of_link true hsub hin)

/-- **Where the IOP passes its tests on the plan, a lot's sub-protocol that is of a kind and lies in
a segment passes its own.** -/
theorem plan_in_segment (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : F.planOk = true)
    {L : Lot} (hL : L ∈ onlineFirstChainBlockTables Z) {b : Block S Cl} (hb : b ∈ L.blocks Bs.G₀)
    (hk : b.place.kind ≠ KindName.frame) {l : Nat} (hl : b.place.link = some l) :
    b.planOk = true := by
  obtain ⟨m, hm, hpl⟩ := stands_in_segment O hL hb hk hl
  exact plan_at_place O hp hL hb hk hm hpl

end ProofFile.Honest.AtPlace

#print axioms ProofFile.Honest.AtPlace.stands_in_segment
#print axioms ProofFile.Honest.AtPlace.plan_in_segment
