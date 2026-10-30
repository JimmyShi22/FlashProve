-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SeatedAppends.lean: WHAT ONE SENDING OF KIND K1 WRITES INTO THE BOOK, AS TWO
APPENDINGS: out of `SeatedBy` (Johnson/Desc/K1/Law/SeatedAtRecord.lean). Two statements with their
proofs. Why: a rule on "the book's places and shapes are a prefix of the plan's lists" (
`seatsPrefix_append`, Johnson/Desc/K12/Coin/BookRides.lean) takes a sending in just this
form.
  `SeatedBy.places`: the book's places behind are those in front, and then, for each message i of
    the place, (the book's trees in front + its tree in the layout, its part).
  `SeatedBy.shapes`: the shapes of the book's trees behind are those in front, and then the
    layout's shapes.
What is not claimed. That a plan's lists go on so. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.SeatedAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain

/-- The book's places behind, as a list. -/
theorem SeatedBy.places {P : Par} {bk bk' : TreeBook} {n r n' r' : Nat}
    (h : SeatedBy P bk n r bk' n' r') :
    bk'.place.toList = bk.place.toList ++ (List.range P.sent.size).map fun i =>
      (bk.trees.size + (layOf P).tree.getD i 0, (layOf P).part.getD i 0) := by
  apply List.ext_getElem?
  intro j
  rw [Array.getElem?_toList]
  by_cases hj : j < bk.place.size
  · rw [h.seated.places j hj, List.getElem?_append_left (by rw [Array.length_toList]; exact hj),
      Array.getElem?_toList]
  · rw [List.getElem?_append_right (by rw [Array.length_toList]; omega), Array.length_toList]
    by_cases hj' : j - bk.place.size < P.sent.size
    · have e := h.seated.new (j - bk.place.size) hj'
      rw [h.seated.step, show bk.place.size + (j - bk.place.size) = j by omega] at e
      rw [e, List.getElem?_map, List.getElem?_range hj']
      rfl
    · rw [Array.getElem?_eq_none (by rw [h.seated.count]; omega),
        List.getElem?_eq_none (by rw [List.length_map, List.length_range]; omega)]

/-- The shapes of the book's trees behind, as a list. -/
theorem SeatedBy.shapes {P : Par} {bk bk' : TreeBook} {n r n' r' : Nat}
    (h : SeatedBy P bk n r bk' n' r') :
    bk'.trees.toList.map (·.shape) = bk.trees.toList.map (·.shape) ++ (layOf P).shapes.toList := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_map, Array.getElem?_toList]
  by_cases hj : j < bk.trees.size
  · rw [h.seated.trees j hj, List.getElem?_append_left
      (by rw [List.length_map, Array.length_toList]; exact hj), List.getElem?_map,
      Array.getElem?_toList]
  · rw [List.getElem?_append_right (by rw [List.length_map, Array.length_toList]; omega),
      List.length_map, Array.length_toList, Array.getElem?_toList]
    by_cases hj' : j - bk.trees.size < (layOf P).shapes.size
    · obtain ⟨t, ht, hs, _⟩ := h.seated.made (j - bk.trees.size) hj'
      rw [show bk.trees.size + (j - bk.trees.size) = j by omega] at ht
      rw [ht, Option.map_some, hs, Array.getElem?_eq_getElem hj', Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem hj']
      rfl
    · rw [Array.getElem?_eq_none (by rw [h.seated.size]; omega),
        Array.getElem?_eq_none (by omega)]
      rfl

end VerifiableInference.Desc.K1
