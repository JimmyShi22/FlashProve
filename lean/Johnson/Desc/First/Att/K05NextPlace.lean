-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05NextPlace.lean: of the driver's own list of the first chain's places
(flatPlacesOf, Johnson/Desc/First/Driver/Chain.lean): behind the place of an attention segment's own
rounds (piece 3, kind K5) stands the same segment's piece 4, of kind K1.

Why. The rule of composition reads its table of rows off a list of places by one number k: the
block's place at k, the next block's at k + 1. Kind K5's laws at the table ask both. Here the second
follows from the first, at every number k, every list of segments and both values of the flag.

Main names:
  `flatMap_next`: of lists alone: where in every chunk q stands behind p, q stands behind p in the
    chunks laid end to end.
  `linkPlaces_next`: in one segment's places.
  `k5_next_place`: **in the whole list.**
A tool. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Driver.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.First (ModelPart linkPlaces flatPlacesOf)

/-- Where in every chunk q stands behind p, it does so in the chunks laid end to end. -/
theorem flatMap_next {α β : Type} (f : α → List β) (p q : β) :
    ∀ (L : List α), (∀ a ∈ L, ∀ j, (f a)[j]? = some p → (f a)[j + 1]? = some q) →
      ∀ k, (L.flatMap f)[k]? = some p → (L.flatMap f)[k + 1]? = some q
  | [], _, k, h => by simp at h
  | a :: L, P, k, h => by
    rw [List.flatMap_cons] at h ⊢
    by_cases hk : k < (f a).length
    · rw [List.getElem?_append_left hk] at h
      have h1 := P a List.mem_cons_self k h
      have hk1 : k + 1 < (f a).length := (List.getElem?_eq_some_iff.1 h1).1
      rw [List.getElem?_append_left hk1]
      exact h1
    · have hk' : (f a).length ≤ k := Nat.le_of_not_lt hk
      rw [List.getElem?_append_right hk'] at h
      rw [List.getElem?_append_right (Nat.le_succ_of_le hk'),
        show k + 1 - (f a).length = k - (f a).length + 1 by omega]
      exact flatMap_next f p q L (fun b hb => P b (List.mem_cons_of_mem _ hb)) _ h

/-- In one segment's places. -/
theorem linkPlaces_next (l : Nat) (sub : ModelPart) (m j : Nat)
    (h : (linkPlaces l sub)[j]? = some ⟨1, some m, 3, .K5⟩) :
    (linkPlaces l sub)[j + 1]? = some ⟨1, some m, 4, .K1⟩ := by
  unfold linkPlaces at h ⊢
  cases sub <;> cases (l == 0) <;>
    simp only [VerifiableInference.Desc.First.kindsBeforeBatching, VerifiableInference.Desc.First.addresses,
      VerifiableInference.Desc.First.closeAddresses, VerifiableInference.Desc.First.closeKinds,
      VerifiableInference.Desc.First.frameAt, VerifiableInference.Desc.First.kindOfModelPart] at h ⊢ <;>
    (rcases j with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | j <;>
      simp_all)

/-- **Behind K5's place stands the segment's piece 4.** -/
theorem k5_next_place (links : List ModelPart) (several : Bool) {k m : Nat}
    (h : (flatPlacesOf links several)[k]? = some ⟨1, some m, 3, .K5⟩) :
    (flatPlacesOf links several)[k + 1]? = some ⟨1, some m, 4, .K1⟩ := by
  unfold flatPlacesOf at h ⊢
  cases k with
  | zero => simp [VerifiableInference.Desc.First.frameAt] at h
  | succ k =>
    rw [List.cons_append, List.cons_append, List.getElem?_cons_succ] at h ⊢
    rw [List.append_assoc] at h ⊢
    by_cases hk : k < (links.zipIdx.flatMap fun x => linkPlaces x.2 x.1).length
    · rw [List.getElem?_append_left hk] at h
      have h1 := flatMap_next (fun x : ModelPart × Nat => linkPlaces x.2 x.1) _ _ links.zipIdx
        (fun a _ j hj => linkPlaces_next a.2 a.1 m j hj) k h
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 h1).1]
      exact h1
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hk)] at h
      have hm := List.mem_of_getElem? h
      rw [List.mem_append] at hm
      rcases hm with hm | hm
      · unfold VerifiableInference.Desc.First.addresses at hm
        obtain ⟨y, -, e⟩ := List.mem_map.1 hm
        exact absurd (congrArg Place.link e) (by simp)
      · rw [List.mem_singleton] at hm
        exact absurd (congrArg Place.link hm) (by simp [VerifiableInference.Desc.First.frameAt])

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.flatMap_next
#print axioms VerifiableInference.Desc.First.Att.P.linkPlaces_next
#print axioms VerifiableInference.Desc.First.Att.P.k5_next_place
