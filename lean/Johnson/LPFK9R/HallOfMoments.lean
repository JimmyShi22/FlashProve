-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/HallOfMoments.lean: THE CLOSED TEST hall OF frameFull_of_facts | full_of_facts
(Johnson/Desc/First/Link/Law/FrameFullOf.lean, FactsAtList.lean: "segment m's list of own numbers
below moment 3 is as long as the shape's list of the link's oracle messages") BROUGHT DOWN TO ONE
PLAIN SENTENCE ON THE REQUEST's SHAPE: every oracle message of link m has a moment below 3.
Theorems.

What is said. msgs := the shape's list of link m's oracle messages (the empty list where the shape
has no such link).
  `ownAt_three_size`: by the texts of another file's terms (FillSent.ownAt, Johnson/Desc/First/
    SentAtMoment.lean; sentDataOf, laterOf, secondNos, thirdNos): the list of own numbers at moment
3
    has as many entries as msgs has messages of moment 0, of moment 1 and of moment 2 together.
  `length_le_three`: a list each of whose members has a moment below 3 is no longer than these three
    counts together.
  `hall_of_moments`: **hall**, at the term ownAt, general in the numbers, the list of segments,
    the list of places and the built links.

Limits. hmom ("every oracle message of link m has a moment below 3") IS A PREMISE: a fact on the
request's shape: SHOWN OF NO SHAPE HERE. Nothing on any state. Nothing on soundness.

-/
import Johnson.Desc.First.SentAtMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFK9
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (ModelPart Numbers)
open VerifiableInference.Desc.First.FillSent

/-- The size of the plan's list of own numbers at moment 3, by its texts. -/
theorem ownAt_three_size (shape : Params.ReqShape) (N : Numbers) (links : List ModelPart)
    (ps : List Place) (built : Array Stages.LinkH) (m : Nat) :
    (ownAt shape N links ps built m 3).size =
      ((((shape.link[m]?.map (·.messages)).getD []).filter fun x => x.moment == 0).length +
        (((shape.link[m]?.map (·.messages)).getD []).filter fun x => x.moment == 1).length) +
        (((shape.link[m]?.map (·.messages)).getD []).filter fun x => x.moment == 2).length := by
  rw [ownAt_three]
  simp [sentData1At, laterOf, sentDataAt, sentDataOf, secondNos, thirdNos]
  omega

/-- A list each of whose members has a moment below 3. -/
theorem length_le_three {α : Type} (f : α → Nat) : ∀ l : List α, (∀ x ∈ l, f x < 3) →
    l.length ≤ ((l.filter fun x => f x == 0).length + (l.filter fun x => f x == 1).length) +
      (l.filter fun x => f x == 2).length
  | [], _ => Nat.le_refl _
  | a :: l, h => by
    have ih := length_le_three f l fun x hx => h x (List.mem_cons_of_mem _ hx)
    have ha : f a < 3 := h a (List.mem_cons_self ..)
    have h3 : f a = 0 ∨ f a = 1 ∨ f a = 2 := by omega
    rcases h3 with e | e | e <;> simp [e] <;> omega

/-- **hall.** -/
theorem hall_of_moments (shape : Params.ReqShape) (N : Numbers) (links : List ModelPart)
    (ps : List Place) (built : Array Stages.LinkH) (m : Nat)
    (hmom : ∀ ms, (shape.link[m]?).map (·.messages) = some ms → ∀ x ∈ ms, x.moment < 3) :
    ∀ ms, (shape.link[m]?).map (·.messages) = some ms →
      ms.length ≤ (ownAt shape N links ps built m 3).size := by
  intro ms hms
  rw [ownAt_three_size, hms]
  exact length_le_three (fun x => x.moment) ms (hmom ms hms)

end LPFK9

#print axioms LPFK9.ownAt_three_size
#print axioms LPFK9.length_le_three
#print axioms LPFK9.hall_of_moments
