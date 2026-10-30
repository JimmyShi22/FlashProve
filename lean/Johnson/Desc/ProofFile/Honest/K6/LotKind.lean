-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/LotKind.lean: EVERY HALF THAT THE HONEST SIDE OF THE LOT "the
output head's own rounds (K6)" LAYS STANDS AT A PLACE OF THE KIND K6: `headLot`
(Honest/K6/Part.lean), at every public test `fits` and every reader `wit`, at every public part and
ground.

WHAT IT IS NOT. NOTHING NEW IS PROVED: `headLot_halves` (Honest/K6/Cut.lean) says already which half
each one is; here its place is read off, and of the place its kind. It does not say that the lot
lays a half: where `fits` rejects, or the lot seats no sub-protocol, the list is empty and all three
statements hold emptily. Nothing on what a half sends. Nothing on any other lot. Nothing on any
property.

  `headLot_place`      the place: the first chain, the last link (number `G.built.size - 1`: 0
                       where nothing is built), piece 4, the kind K6
  `headLot_kind`       its kind
  `headLot_kind_id`    the same at `headFitsB` and `headWit' id id` (Honest/K6/Wit.lean: that lot
                       is `headLotAt id id`): both shared readers are the identity: so the letter
                       Tr is `Cells` and W₀ is `Weights` (Honest/ForKinds.lean)

No premise. Called: `headLot_halves`; `headHalf`, `headPlace` (Honest/K6/Part.lean) by unfolding.
-/
import Johnson.Desc.ProofFile.Honest.K6.Cut
import Johnson.Desc.ProofFile.Honest.K6.Wit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6

/-- **The place of each half that the lot's honest side lays**: piece 4 of the last link. No
premise. Where no half is laid it holds emptily. -/
theorem headLot_place {W₀ Rc Tr X : Type} (fits : Pub → Ground → Bool)
    (wit : Pub → Ground → Local W₀ Rc Inst Tr → HeadAsk) (Z : Pub) (G : Ground) :
    ∀ x ∈ (headLot (X := X) fits wit).halves Z G, x.place = headPlace (G.built.size - 1) 4 := by
  intro x hx
  rw [headLot_halves fits wit Z G x hx]
  rfl

/-- **Its kind is K6.** No premise. -/
theorem headLot_kind {W₀ Rc Tr X : Type} (fits : Pub → Ground → Bool)
    (wit : Pub → Ground → Local W₀ Rc Inst Tr → HeadAsk) (Z : Pub) (G : Ground) :
    ∀ x ∈ (headLot (X := X) fits wit).halves Z G, x.place.kind = .K6 := by
  intro x hx
  rw [headLot_place fits wit Z G x hx]
  rfl

/-- The same at the lot's own public test and at its reader with both shared readers the identity.
No premise. -/
theorem headLot_kind_id {Rc X : Type} (Z : Pub) (G : Ground) :
    ∀ x ∈ (headLot headFitsB (headWit' id id) :
        HLot (Local Weights Rc Inst Cells) (Local Weights Rc Inst Cells) X).halves Z G,
      x.place.kind = .K6 :=
  headLot_kind _ _ Z G

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.headLot_place
#print axioms ProofFile.Honest.K6.headLot_kind
#print axioms ProofFile.Honest.K6.headLot_kind_id
